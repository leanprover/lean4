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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3_value;
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
static lean_once_cell_t l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5;
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
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "abs"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__4_value),LEAN_SCALAR_PTR_LITERAL(11, 180, 28, 55, 197, 20, 206, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 166, 239, 19, 130, 98, 40, 185)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_LetValue_toMono___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4_value),LEAN_SCALAR_PTR_LITERAL(9, 137, 41, 185, 216, 152, 145, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_13669__overap_808_; lean_object* v___x_809_; 
v___x_805_ = l_StateRefT_x27_instMonad___redArg(v___x_804_);
v___x_806_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_807_ = l_instInhabitedOfMonad___redArg(v___x_805_, v___x_806_);
v___x_13669__overap_808_ = lean_panic_fn_borrowed(v___x_807_, v_msg_749_);
lean_dec(v___x_807_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
v___x_809_ = lean_apply_6(v___x_13669__overap_808_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, lean_box(0));
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
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_43620__overap_1699_; lean_object* v___x_1700_; 
v___x_1696_ = l_StateRefT_x27_instMonad___redArg(v___x_1695_);
v___x_1697_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1698_ = l_instInhabitedOfMonad___redArg(v___x_1696_, v___x_1697_);
v___x_43620__overap_1699_ = lean_panic_fn_borrowed(v___x_1698_, v_msg_1640_);
lean_dec(v___x_1698_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
lean_inc(v___y_1643_);
lean_inc_ref(v___y_1642_);
lean_inc(v___y_1641_);
v___x_1700_ = lean_apply_6(v___x_43620__overap_1699_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, lean_box(0));
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
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_43635__overap_1785_; lean_object* v___x_1786_; 
v___x_1782_ = l_StateRefT_x27_instMonad___redArg(v___x_1781_);
v___x_1783_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1784_ = l_instInhabitedOfMonad___redArg(v___x_1782_, v___x_1783_);
v___x_43635__overap_1785_ = lean_panic_fn_borrowed(v___x_1784_, v_msg_1726_);
lean_dec(v___x_1784_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1729_);
lean_inc_ref(v___y_1728_);
lean_inc(v___y_1727_);
v___x_1786_ = lean_apply_6(v___x_43635__overap_1785_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, lean_box(0));
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
v___x_1813_ = lean_unsigned_to_nat(411u);
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
v___x_1871_ = lean_unsigned_to_nat(365u);
v___x_1872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1873_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1874_ = l_mkPanicMessageWithDecl(v___x_1873_, v___x_1872_, v___x_1871_, v___x_1870_, v___x_1869_);
return v___x_1874_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1931_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1932_ = lean_unsigned_to_nat(2u);
v___x_1933_ = lean_unsigned_to_nat(348u);
v___x_1934_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1935_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1936_ = l_mkPanicMessageWithDecl(v___x_1935_, v___x_1934_, v___x_1933_, v___x_1932_, v___x_1931_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1938_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1939_ = lean_unsigned_to_nat(2u);
v___x_1940_ = lean_unsigned_to_nat(350u);
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1943_ = l_mkPanicMessageWithDecl(v___x_1942_, v___x_1941_, v___x_1940_, v___x_1939_, v___x_1938_);
return v___x_1943_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1946_ = lean_unsigned_to_nat(2u);
v___x_1947_ = lean_unsigned_to_nat(351u);
v___x_1948_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1949_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1950_ = l_mkPanicMessageWithDecl(v___x_1949_, v___x_1948_, v___x_1947_, v___x_1946_, v___x_1945_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1951_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1952_ = lean_unsigned_to_nat(41u);
v___x_1953_ = lean_unsigned_to_nat(349u);
v___x_1954_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1955_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1956_ = l_mkPanicMessageWithDecl(v___x_1955_, v___x_1954_, v___x_1953_, v___x_1952_, v___x_1951_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1957_, lean_object* v_c_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v_discr_1965_; lean_object* v_alts_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2044_; 
v_discr_1965_ = lean_ctor_get(v_c_1958_, 2);
v_alts_1966_ = lean_ctor_get(v_c_1958_, 3);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_c_1958_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; lean_object* v_unused_2046_; 
v_unused_2045_ = lean_ctor_get(v_c_1958_, 1);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_c_1958_, 0);
lean_dec(v_unused_2046_);
v___x_1968_ = v_c_1958_;
v_isShared_1969_ = v_isSharedCheck_2044_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_alts_1966_);
lean_inc(v_discr_1965_);
lean_dec(v_c_1958_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2044_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1970_ = lean_array_get_size(v_alts_1966_);
v___x_1971_ = lean_unsigned_to_nat(1u);
v___x_1972_ = lean_nat_dec_eq(v___x_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_del_object(v___x_1968_);
lean_dec_ref(v_alts_1966_);
lean_dec(v_discr_1965_);
v___x_1973_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1974_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1973_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1974_;
}
else
{
uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = 0;
v___x_1976_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = lean_array_get(v___x_1976_, v_alts_1966_, v___x_1977_);
lean_dec_ref(v_alts_1966_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_ctorName_1979_; lean_object* v_params_1980_; lean_object* v_code_1981_; lean_object* v_ctorName_1982_; lean_object* v_fieldIdx_1983_; uint8_t v___x_1984_; 
v_ctorName_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_ctorName_1979_);
v_params_1980_ = lean_ctor_get(v___x_1978_, 1);
lean_inc_ref(v_params_1980_);
v_code_1981_ = lean_ctor_get(v___x_1978_, 2);
lean_inc_ref(v_code_1981_);
lean_dec_ref_known(v___x_1978_, 3);
v_ctorName_1982_ = lean_ctor_get(v_info_1957_, 0);
v_fieldIdx_1983_ = lean_ctor_get(v_info_1957_, 2);
v___x_1984_ = lean_name_eq(v_ctorName_1979_, v_ctorName_1982_);
lean_dec(v_ctorName_1979_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_code_1981_);
lean_dec_ref(v_params_1980_);
lean_del_object(v___x_1968_);
lean_dec(v_discr_1965_);
v___x_1985_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1986_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1985_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1986_;
}
else
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = lean_array_get_size(v_params_1980_);
v___x_1988_ = lean_nat_dec_lt(v_fieldIdx_1983_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec_ref(v_code_1981_);
lean_dec_ref(v_params_1980_);
lean_del_object(v___x_1968_);
lean_dec(v_discr_1965_);
v___x_1989_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1990_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1989_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_1992_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1975_, v_params_1980_, v_a_1961_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_p_1993_; lean_object* v_fvarId_1994_; lean_object* v_binderName_1995_; lean_object* v_type_1996_; lean_object* v___x_1997_; 
lean_dec_ref_known(v___x_1992_, 1);
v_p_1993_ = lean_array_get(v___x_1991_, v_params_1980_, v_fieldIdx_1983_);
lean_dec_ref(v_params_1980_);
v_fvarId_1994_ = lean_ctor_get(v_p_1993_, 0);
lean_inc(v_fvarId_1994_);
v_binderName_1995_ = lean_ctor_get(v_p_1993_, 1);
lean_inc(v_binderName_1995_);
v_type_1996_ = lean_ctor_get(v_p_1993_, 2);
lean_inc_ref(v_type_1996_);
lean_dec(v_p_1993_);
v___x_1997_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1996_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_1999_; lean_object* v_lctx_2000_; lean_object* v_nextIdx_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2025_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = lean_st_ref_take(v_a_1961_);
v_lctx_2000_ = lean_ctor_get(v___x_1999_, 0);
v_nextIdx_2001_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2003_ = v___x_1999_;
v_isShared_2004_ = v_isSharedCheck_2025_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_nextIdx_2001_);
lean_inc(v_lctx_2000_);
lean_dec(v___x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2025_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2005_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_2006_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_discr_1965_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 3, v___x_2006_);
lean_ctor_set(v___x_1968_, 2, v_a_1998_);
lean_ctor_set(v___x_1968_, 1, v_binderName_1995_);
lean_ctor_set(v___x_1968_, 0, v_fvarId_1994_);
v___x_2008_ = v___x_1968_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_fvarId_1994_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_binderName_1995_);
lean_ctor_set(v_reuseFailAlloc_2024_, 2, v_a_1998_);
lean_ctor_set(v_reuseFailAlloc_2024_, 3, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_inc_ref(v___x_2008_);
v___x_2009_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1975_, v_lctx_2000_, v___x_2008_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2009_);
v___x_2011_ = v___x_2003_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_nextIdx_2001_);
v___x_2011_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = lean_st_ref_set(v_a_1961_, v___x_2011_);
v___x_2013_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1981_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2022_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2016_ = v___x_2013_;
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2013_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2022_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2008_);
lean_ctor_set(v___x_2018_, 1, v_a_2014_);
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 0, v___x_2018_);
v___x_2020_ = v___x_2016_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_dec_ref(v___x_2008_);
return v___x_2013_;
}
}
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_binderName_1995_);
lean_dec(v_fvarId_1994_);
lean_dec_ref(v_code_1981_);
lean_del_object(v___x_1968_);
lean_dec(v_discr_1965_);
v_a_2026_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_1997_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_1997_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref(v_code_1981_);
lean_dec_ref(v_params_1980_);
lean_del_object(v___x_1968_);
lean_dec(v_discr_1965_);
v_a_2034_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_1992_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_1992_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec(v___x_1978_);
lean_del_object(v___x_1968_);
lean_dec(v_discr_1965_);
v___x_2042_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_2043_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2042_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
return v___x_2043_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_2049_ = lean_unsigned_to_nat(70u);
v___x_2050_ = lean_unsigned_to_nat(421u);
v___x_2051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_2052_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2053_ = l_mkPanicMessageWithDecl(v___x_2052_, v___x_2051_, v___x_2050_, v___x_2049_, v___x_2048_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_2057_, uint8_t v___x_2058_, size_t v_sz_2059_, size_t v_i_2060_, lean_object* v_bs_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_usize_dec_lt(v_i_2060_, v_sz_2059_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref(v___x_2057_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_bs_2061_);
return v___x_2069_;
}
else
{
lean_object* v_v_2070_; lean_object* v___x_2071_; lean_object* v_bs_x27_2072_; lean_object* v_a_2074_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; 
v_v_2070_ = lean_array_uget(v_bs_2061_, v_i_2060_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v_bs_x27_2072_ = lean_array_uset(v_bs_2061_, v_i_2060_, v___x_2071_);
if (lean_obj_tag(v_v_2070_) == 0)
{
lean_object* v_ctorName_2096_; lean_object* v_params_2097_; lean_object* v_code_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2136_; 
v_ctorName_2096_ = lean_ctor_get(v_v_2070_, 0);
v_params_2097_ = lean_ctor_get(v_v_2070_, 1);
v_code_2098_ = lean_ctor_get(v_v_2070_, 2);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_v_2070_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2100_ = v_v_2070_;
v_isShared_2101_ = v_isSharedCheck_2136_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_code_2098_);
lean_inc(v_params_2097_);
lean_inc(v_ctorName_2096_);
lean_dec(v_v_2070_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2136_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_2103_ = l_Lean_Name_append(v_ctorName_2096_, v___x_2102_);
lean_inc(v___x_2103_);
lean_inc_ref(v___x_2057_);
v___x_2104_ = l_Lean_Environment_find_x3f(v___x_2057_, v___x_2103_, v___x_2058_);
if (lean_obj_tag(v___x_2104_) == 1)
{
lean_object* v_val_2105_; 
v_val_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v___x_2104_, 1);
if (lean_obj_tag(v_val_2105_) == 6)
{
lean_object* v_val_2106_; lean_object* v_toConstantVal_2107_; lean_object* v_numParams_2108_; lean_object* v_numFields_2109_; lean_object* v_type_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_val_2106_ = lean_ctor_get(v_val_2105_, 0);
lean_inc_ref(v_val_2106_);
lean_dec_ref_known(v_val_2105_, 1);
v_toConstantVal_2107_ = lean_ctor_get(v_val_2106_, 0);
lean_inc_ref(v_toConstantVal_2107_);
v_numParams_2108_ = lean_ctor_get(v_val_2106_, 3);
lean_inc(v_numParams_2108_);
v_numFields_2109_ = lean_ctor_get(v_val_2106_, 4);
lean_inc(v_numFields_2109_);
lean_dec_ref(v_val_2106_);
v_type_2110_ = lean_ctor_get(v_toConstantVal_2107_, 2);
lean_inc_ref(v_type_2110_);
lean_dec_ref(v_toConstantVal_2107_);
v___x_2111_ = lean_array_get_size(v_params_2097_);
v___x_2112_ = lean_nat_sub(v_numFields_2109_, v___x_2111_);
lean_dec(v_numFields_2109_);
v___x_2113_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_2110_, v_numParams_2108_, v___x_2112_, v_params_2097_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec_ref(v_params_2097_);
lean_dec(v___x_2112_);
lean_dec(v_numParams_2108_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2098_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2115_, 1);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 2, v_a_2116_);
lean_ctor_set(v___x_2100_, 1, v_a_2114_);
lean_ctor_set(v___x_2100_, 0, v___x_2103_);
v___x_2118_ = v___x_2100_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_a_2114_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_a_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
v_a_2074_ = v___x_2118_;
goto v___jp_2073_;
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2114_);
lean_dec(v___x_2103_);
lean_del_object(v___x_2100_);
lean_dec_ref(v_bs_x27_2072_);
lean_dec_ref(v___x_2057_);
v_a_2120_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2115_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2115_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v___x_2103_);
lean_del_object(v___x_2100_);
lean_dec_ref(v_code_2098_);
lean_dec_ref(v_bs_x27_2072_);
lean_dec_ref(v___x_2057_);
v_a_2128_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2113_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2113_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_dec(v_val_2105_);
lean_dec(v___x_2103_);
lean_del_object(v___x_2100_);
lean_dec_ref(v_code_2098_);
lean_dec_ref(v_params_2097_);
v___y_2080_ = v___y_2062_;
v___y_2081_ = v___y_2063_;
v___y_2082_ = v___y_2064_;
v___y_2083_ = v___y_2065_;
v___y_2084_ = v___y_2066_;
goto v___jp_2079_;
}
}
else
{
lean_dec(v___x_2104_);
lean_dec(v___x_2103_);
lean_del_object(v___x_2100_);
lean_dec_ref(v_code_2098_);
lean_dec_ref(v_params_2097_);
v___y_2080_ = v___y_2062_;
v___y_2081_ = v___y_2063_;
v___y_2082_ = v___y_2064_;
v___y_2083_ = v___y_2065_;
v___y_2084_ = v___y_2066_;
goto v___jp_2079_;
}
}
}
else
{
lean_object* v_code_2137_; lean_object* v___x_2138_; 
v_code_2137_ = lean_ctor_get(v_v_2070_, 0);
lean_inc_ref(v_code_2137_);
v___x_2138_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2137_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v___x_2140_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2070_, v_a_2139_);
v_a_2074_ = v___x_2140_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref_known(v_v_2070_, 1);
lean_dec_ref(v_bs_x27_2072_);
lean_dec_ref(v___x_2057_);
v_a_2141_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2138_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2138_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
v___jp_2073_:
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)1ULL);
v___x_2076_ = lean_usize_add(v_i_2060_, v___x_2075_);
v___x_2077_ = lean_array_uset(v_bs_x27_2072_, v_i_2060_, v_a_2074_);
v_i_2060_ = v___x_2076_;
v_bs_2061_ = v___x_2077_;
goto _start;
}
v___jp_2079_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_2086_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_2085_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v_a_2074_ = v_a_2087_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_bs_x27_2072_);
lean_dec_ref(v___x_2057_);
v_a_2088_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_2149_, size_t v_i_2150_, lean_object* v_bs_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v___x_2158_; 
v___x_2158_ = lean_usize_dec_lt(v_i_2150_, v_sz_2149_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; 
v___x_2159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_bs_2151_);
return v___x_2159_;
}
else
{
lean_object* v_v_2160_; lean_object* v___x_2161_; lean_object* v_bs_x27_2162_; lean_object* v_a_2164_; 
v_v_2160_ = lean_array_uget(v_bs_2151_, v_i_2150_);
v___x_2161_ = lean_unsigned_to_nat(0u);
v_bs_x27_2162_ = lean_array_uset(v_bs_2151_, v_i_2150_, v___x_2161_);
if (lean_obj_tag(v_v_2160_) == 0)
{
lean_object* v_params_2169_; lean_object* v_code_2170_; size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v_params_2169_ = lean_ctor_get(v_v_2160_, 1);
v_code_2170_ = lean_ctor_get(v_v_2160_, 2);
v_sz_2171_ = lean_array_size(v_params_2169_);
v___x_2172_ = ((size_t)0ULL);
lean_inc_ref(v_params_2169_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2171_, v___x_2172_, v_params_2169_, v___y_2152_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
lean_inc_ref(v_code_2170_);
v___x_2175_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2170_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = 0;
v___x_2178_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_2177_, v_v_2160_, v_a_2174_, v_a_2176_);
v_a_2164_ = v___x_2178_;
goto v___jp_2163_;
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2174_);
lean_dec_ref_known(v_v_2160_, 3);
lean_dec_ref(v_bs_x27_2162_);
v_a_2179_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2175_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2175_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_2160_, 3);
lean_dec_ref(v_bs_x27_2162_);
return v___x_2173_;
}
}
else
{
lean_object* v_code_2187_; lean_object* v___x_2188_; 
v_code_2187_ = lean_ctor_get(v_v_2160_, 0);
lean_inc_ref(v_code_2187_);
v___x_2188_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2187_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2160_, v_a_2189_);
v_a_2164_ = v___x_2190_;
goto v___jp_2163_;
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref_known(v_v_2160_, 1);
lean_dec_ref(v_bs_x27_2162_);
v_a_2191_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2188_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2188_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
v___jp_2163_:
{
size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_add(v_i_2150_, v___x_2165_);
v___x_2167_ = lean_array_uset(v_bs_x27_2162_, v_i_2150_, v_a_2164_);
v_i_2150_ = v___x_2166_;
v_bs_2151_ = v___x_2167_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2200_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2201_ = lean_unsigned_to_nat(2u);
v___x_2202_ = lean_unsigned_to_nat(337u);
v___x_2203_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2204_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2205_ = l_mkPanicMessageWithDecl(v___x_2204_, v___x_2203_, v___x_2202_, v___x_2201_, v___x_2200_);
return v___x_2205_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_unsigned_to_nat(2u);
v___x_2212_ = lean_mk_empty_array_with_capacity(v___x_2211_);
v___x_2213_ = lean_array_push(v___x_2212_, v___x_2210_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2214_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2215_ = lean_unsigned_to_nat(34u);
v___x_2216_ = lean_unsigned_to_nat(338u);
v___x_2217_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2218_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2219_ = l_mkPanicMessageWithDecl(v___x_2218_, v___x_2217_, v___x_2216_, v___x_2215_, v___x_2214_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v_discr_2227_; lean_object* v_alts_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2297_; 
v_discr_2227_ = lean_ctor_get(v_c_2220_, 2);
v_alts_2228_ = lean_ctor_get(v_c_2220_, 3);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_c_2220_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; lean_object* v_unused_2299_; 
v_unused_2298_ = lean_ctor_get(v_c_2220_, 1);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_c_2220_, 0);
lean_dec(v_unused_2299_);
v___x_2230_ = v_c_2220_;
v_isShared_2231_ = v_isSharedCheck_2297_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_alts_2228_);
lean_inc(v_discr_2227_);
lean_dec(v_c_2220_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2297_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2232_ = lean_array_get_size(v_alts_2228_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_dec_eq(v___x_2232_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_del_object(v___x_2230_);
lean_dec_ref(v_alts_2228_);
lean_dec(v_discr_2227_);
v___x_2235_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_2236_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2235_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2236_;
}
else
{
uint8_t v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = 0;
v___x_2238_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_array_get(v___x_2238_, v_alts_2228_, v___x_2239_);
lean_dec_ref(v_alts_2228_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_params_2241_; lean_object* v_code_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2293_; 
v_params_2241_ = lean_ctor_get(v___x_2240_, 1);
v_code_2242_ = lean_ctor_get(v___x_2240_, 2);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; 
v_unused_2294_ = lean_ctor_get(v___x_2240_, 0);
lean_dec(v_unused_2294_);
v___x_2244_ = v___x_2240_;
v_isShared_2245_ = v_isSharedCheck_2293_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_code_2242_);
lean_inc(v_params_2241_);
lean_dec(v___x_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2293_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2237_, v_params_2241_, v_a_2223_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_fvarId_2250_; lean_object* v_binderName_2251_; lean_object* v_lctx_2252_; lean_object* v_nextIdx_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2284_; 
lean_dec_ref_known(v___x_2246_, 1);
v___x_2247_ = lean_st_ref_take(v_a_2223_);
v___x_2248_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2249_ = lean_array_get(v___x_2248_, v_params_2241_, v___x_2239_);
lean_dec_ref(v_params_2241_);
v_fvarId_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_fvarId_2250_);
v_binderName_2251_ = lean_ctor_get(v___x_2249_, 1);
lean_inc(v_binderName_2251_);
lean_dec(v___x_2249_);
v_lctx_2252_ = lean_ctor_get(v___x_2247_, 0);
v_nextIdx_2253_ = lean_ctor_get(v___x_2247_, 1);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2255_ = v___x_2247_;
v_isShared_2256_ = v_isSharedCheck_2284_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_nextIdx_2253_);
lean_inc(v_lctx_2252_);
lean_dec(v___x_2247_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2284_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2263_; 
v___x_2257_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_2258_ = lean_box(0);
v___x_2259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2259_, 0, v_discr_2227_);
v___x_2260_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2261_ = lean_array_push(v___x_2260_, v___x_2259_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 3);
lean_ctor_set(v___x_2244_, 2, v___x_2261_);
lean_ctor_set(v___x_2244_, 1, v___x_2258_);
lean_ctor_set(v___x_2244_, 0, v___x_2257_);
v___x_2263_ = v___x_2244_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v___x_2261_);
v___x_2263_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 3, v___x_2263_);
lean_ctor_set(v___x_2230_, 2, v___x_2264_);
lean_ctor_set(v___x_2230_, 1, v_binderName_2251_);
lean_ctor_set(v___x_2230_, 0, v_fvarId_2250_);
v___x_2266_ = v___x_2230_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_fvarId_2250_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_binderName_2251_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v___x_2264_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v___x_2263_);
v___x_2266_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_inc_ref(v___x_2266_);
v___x_2267_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2237_, v_lctx_2252_, v___x_2266_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2267_);
v___x_2269_ = v___x_2255_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_nextIdx_2253_);
v___x_2269_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = lean_st_ref_set(v_a_2223_, v___x_2269_);
v___x_2271_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2242_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2266_);
lean_ctor_set(v___x_2276_, 1, v_a_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
else
{
lean_dec_ref(v___x_2266_);
return v___x_2271_;
}
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2244_);
lean_dec_ref(v_code_2242_);
lean_dec_ref(v_params_2241_);
lean_del_object(v___x_2230_);
lean_dec(v_discr_2227_);
v_a_2285_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2246_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2246_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec(v___x_2240_);
lean_del_object(v___x_2230_);
lean_dec(v_discr_2227_);
v___x_2295_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_2296_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2295_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2296_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2302_ = lean_unsigned_to_nat(2u);
v___x_2303_ = lean_unsigned_to_nat(317u);
v___x_2304_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2305_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2306_ = l_mkPanicMessageWithDecl(v___x_2305_, v___x_2304_, v___x_2303_, v___x_2302_, v___x_2301_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_box(0);
v___x_2314_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_2315_ = l_Lean_Expr_const___override(v___x_2314_, v___x_2313_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2316_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2317_ = lean_unsigned_to_nat(34u);
v___x_2318_ = lean_unsigned_to_nat(318u);
v___x_2319_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2320_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2321_ = l_mkPanicMessageWithDecl(v___x_2320_, v___x_2319_, v___x_2318_, v___x_2317_, v___x_2316_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_discr_2329_; lean_object* v_alts_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v_discr_2329_ = lean_ctor_get(v_c_2322_, 2);
v_alts_2330_ = lean_ctor_get(v_c_2322_, 3);
v___x_2331_ = lean_array_get_size(v_alts_2330_);
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_dec_eq(v___x_2331_, v___x_2332_);
if (v___x_2333_ == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_2335_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2334_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
return v___x_2335_;
}
else
{
uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2336_ = 0;
v___x_2337_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_array_get(v___x_2337_, v_alts_2330_, v___x_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_params_2340_; lean_object* v_code_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2438_; 
v_params_2340_ = lean_ctor_get(v___x_2339_, 1);
v_code_2341_ = lean_ctor_get(v___x_2339_, 2);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; 
v_unused_2439_ = lean_ctor_get(v___x_2339_, 0);
lean_dec(v_unused_2439_);
v___x_2343_ = v___x_2339_;
v_isShared_2344_ = v_isSharedCheck_2438_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_code_2341_);
lean_inc(v_params_2340_);
lean_dec(v___x_2339_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2438_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2336_, v_params_2340_, v_a_2325_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_dec_ref_known(v___x_2345_, 1);
v___x_2346_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2347_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2346_, v_a_2325_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
lean_inc(v_discr_2329_);
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_discr_2329_);
v___x_2351_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2352_ = lean_box(0);
v___x_2353_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2354_ = lean_array_push(v___x_2353_, v___x_2350_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 3);
lean_ctor_set(v___x_2343_, 2, v___x_2354_);
lean_ctor_set(v___x_2343_, 1, v___x_2352_);
lean_ctor_set(v___x_2343_, 0, v___x_2351_);
v___x_2356_ = v___x_2343_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2358_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2336_, v_a_2348_, v___x_2357_, v___x_2356_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2361_ = 0;
v___x_2362_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_2336_, v___x_2360_, v___x_2361_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = l_Lean_mkArrow(v___x_2360_, v___x_2357_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v_fvarId_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_fvarId_2369_; lean_object* v_binderName_2370_; lean_object* v_lctx_2371_; lean_object* v_nextIdx_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2396_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2364_, 1);
v_fvarId_2366_ = lean_ctor_get(v_a_2359_, 0);
v___x_2367_ = lean_st_ref_take(v_a_2325_);
v___x_2368_ = lean_array_get(v___x_2349_, v_params_2340_, v___x_2338_);
lean_dec_ref(v_params_2340_);
v_fvarId_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_fvarId_2369_);
v_binderName_2370_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_binderName_2370_);
lean_dec(v___x_2368_);
v_lctx_2371_ = lean_ctor_get(v___x_2367_, 0);
v_nextIdx_2372_ = lean_ctor_get(v___x_2367_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2374_ = v___x_2367_;
v_isShared_2375_ = v_isSharedCheck_2396_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_nextIdx_2372_);
lean_inc(v_lctx_2371_);
lean_dec(v___x_2367_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2396_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_inc(v_fvarId_2366_);
v___x_2376_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_fvarId_2366_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v_a_2359_);
lean_ctor_set(v___x_2377_, 1, v___x_2376_);
v___x_2378_ = lean_mk_empty_array_with_capacity(v___x_2332_);
v___x_2379_ = lean_array_push(v___x_2378_, v_a_2363_);
v___x_2380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2380_, 0, v_fvarId_2369_);
lean_ctor_set(v___x_2380_, 1, v_binderName_2370_);
lean_ctor_set(v___x_2380_, 2, v___x_2379_);
lean_ctor_set(v___x_2380_, 3, v_a_2365_);
lean_ctor_set(v___x_2380_, 4, v___x_2377_);
lean_inc_ref(v___x_2380_);
v___x_2381_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2336_, v_lctx_2371_, v___x_2380_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2381_);
v___x_2383_ = v___x_2374_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_nextIdx_2372_);
v___x_2383_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_st_ref_set(v_a_2325_, v___x_2383_);
v___x_2385_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2341_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2394_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2394_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2380_);
lean_ctor_set(v___x_2390_, 1, v_a_2386_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v___x_2390_);
v___x_2392_ = v___x_2388_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
else
{
lean_dec_ref_known(v___x_2380_, 5);
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v_a_2363_);
lean_dec(v_a_2359_);
lean_dec_ref(v_code_2341_);
lean_dec_ref(v_params_2340_);
v_a_2397_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2364_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2364_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v_a_2359_);
lean_dec_ref(v_code_2341_);
lean_dec_ref(v_params_2340_);
v_a_2405_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2362_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2362_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v_code_2341_);
lean_dec_ref(v_params_2340_);
v_a_2413_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2358_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2358_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_del_object(v___x_2343_);
lean_dec_ref(v_code_2341_);
lean_dec_ref(v_params_2340_);
v_a_2422_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2347_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2347_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_del_object(v___x_2343_);
lean_dec_ref(v_code_2341_);
lean_dec_ref(v_params_2340_);
v_a_2430_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2345_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2345_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec(v___x_2339_);
v___x_2440_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2441_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2440_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
return v___x_2441_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2443_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2444_ = lean_unsigned_to_nat(2u);
v___x_2445_ = lean_unsigned_to_nat(306u);
v___x_2446_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2447_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2448_ = l_mkPanicMessageWithDecl(v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_, v___x_2443_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2453_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2454_ = lean_unsigned_to_nat(34u);
v___x_2455_ = lean_unsigned_to_nat(307u);
v___x_2456_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2457_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2458_ = l_mkPanicMessageWithDecl(v___x_2457_, v___x_2456_, v___x_2455_, v___x_2454_, v___x_2453_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_discr_2466_; lean_object* v_alts_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2536_; 
v_discr_2466_ = lean_ctor_get(v_c_2459_, 2);
v_alts_2467_ = lean_ctor_get(v_c_2459_, 3);
v_isSharedCheck_2536_ = !lean_is_exclusive(v_c_2459_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; lean_object* v_unused_2538_; 
v_unused_2537_ = lean_ctor_get(v_c_2459_, 1);
lean_dec(v_unused_2537_);
v_unused_2538_ = lean_ctor_get(v_c_2459_, 0);
lean_dec(v_unused_2538_);
v___x_2469_ = v_c_2459_;
v_isShared_2470_ = v_isSharedCheck_2536_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_alts_2467_);
lean_inc(v_discr_2466_);
lean_dec(v_c_2459_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2536_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2471_ = lean_array_get_size(v_alts_2467_);
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_dec_eq(v___x_2471_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_del_object(v___x_2469_);
lean_dec_ref(v_alts_2467_);
lean_dec(v_discr_2466_);
v___x_2474_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2475_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2474_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
return v___x_2475_;
}
else
{
uint8_t v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = 0;
v___x_2477_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_array_get(v___x_2477_, v_alts_2467_, v___x_2478_);
lean_dec_ref(v_alts_2467_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_params_2480_; lean_object* v_code_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2532_; 
v_params_2480_ = lean_ctor_get(v___x_2479_, 1);
v_code_2481_ = lean_ctor_get(v___x_2479_, 2);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2479_, 0);
lean_dec(v_unused_2533_);
v___x_2483_ = v___x_2479_;
v_isShared_2484_ = v_isSharedCheck_2532_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_code_2481_);
lean_inc(v_params_2480_);
lean_dec(v___x_2479_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2532_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2476_, v_params_2480_, v_a_2462_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_fvarId_2489_; lean_object* v_binderName_2490_; lean_object* v_lctx_2491_; lean_object* v_nextIdx_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2523_; 
lean_dec_ref_known(v___x_2485_, 1);
v___x_2486_ = lean_st_ref_take(v_a_2462_);
v___x_2487_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2488_ = lean_array_get(v___x_2487_, v_params_2480_, v___x_2478_);
lean_dec_ref(v_params_2480_);
v_fvarId_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_fvarId_2489_);
v_binderName_2490_ = lean_ctor_get(v___x_2488_, 1);
lean_inc(v_binderName_2490_);
lean_dec(v___x_2488_);
v_lctx_2491_ = lean_ctor_get(v___x_2486_, 0);
v_nextIdx_2492_ = lean_ctor_get(v___x_2486_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2494_ = v___x_2486_;
v_isShared_2495_ = v_isSharedCheck_2523_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_nextIdx_2492_);
lean_inc(v_lctx_2491_);
lean_dec(v___x_2486_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2523_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2496_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2497_ = lean_box(0);
v___x_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2498_, 0, v_discr_2466_);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2472_);
v___x_2500_ = lean_array_push(v___x_2499_, v___x_2498_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 3);
lean_ctor_set(v___x_2483_, 2, v___x_2500_);
lean_ctor_set(v___x_2483_, 1, v___x_2497_);
lean_ctor_set(v___x_2483_, 0, v___x_2496_);
v___x_2502_ = v___x_2483_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2496_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2503_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 3, v___x_2502_);
lean_ctor_set(v___x_2469_, 2, v___x_2503_);
lean_ctor_set(v___x_2469_, 1, v_binderName_2490_);
lean_ctor_set(v___x_2469_, 0, v_fvarId_2489_);
v___x_2505_ = v___x_2469_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_fvarId_2489_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_binderName_2490_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v___x_2502_);
v___x_2505_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_inc_ref(v___x_2505_);
v___x_2506_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2476_, v_lctx_2491_, v___x_2505_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2506_);
v___x_2508_ = v___x_2494_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_nextIdx_2492_);
v___x_2508_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_st_ref_set(v_a_2462_, v___x_2508_);
v___x_2510_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2481_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2519_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2505_);
lean_ctor_set(v___x_2515_, 1, v_a_2511_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_dec_ref(v___x_2505_);
return v___x_2510_;
}
}
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_del_object(v___x_2483_);
lean_dec_ref(v_code_2481_);
lean_dec_ref(v_params_2480_);
lean_del_object(v___x_2469_);
lean_dec(v_discr_2466_);
v_a_2524_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2485_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2485_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
else
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v___x_2479_);
lean_del_object(v___x_2469_);
lean_dec(v_discr_2466_);
v___x_2534_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2535_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2534_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
return v___x_2535_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2540_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2541_ = lean_unsigned_to_nat(2u);
v___x_2542_ = lean_unsigned_to_nat(295u);
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2544_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2545_ = l_mkPanicMessageWithDecl(v___x_2544_, v___x_2543_, v___x_2542_, v___x_2541_, v___x_2540_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2549_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2550_ = lean_unsigned_to_nat(34u);
v___x_2551_ = lean_unsigned_to_nat(296u);
v___x_2552_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2553_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2554_ = l_mkPanicMessageWithDecl(v___x_2553_, v___x_2552_, v___x_2551_, v___x_2550_, v___x_2549_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_discr_2562_; lean_object* v_alts_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2632_; 
v_discr_2562_ = lean_ctor_get(v_c_2555_, 2);
v_alts_2563_ = lean_ctor_get(v_c_2555_, 3);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_c_2555_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; lean_object* v_unused_2634_; 
v_unused_2633_ = lean_ctor_get(v_c_2555_, 1);
lean_dec(v_unused_2633_);
v_unused_2634_ = lean_ctor_get(v_c_2555_, 0);
lean_dec(v_unused_2634_);
v___x_2565_ = v_c_2555_;
v_isShared_2566_ = v_isSharedCheck_2632_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_alts_2563_);
lean_inc(v_discr_2562_);
lean_dec(v_c_2555_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2632_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2567_ = lean_array_get_size(v_alts_2563_);
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = lean_nat_dec_eq(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_del_object(v___x_2565_);
lean_dec_ref(v_alts_2563_);
lean_dec(v_discr_2562_);
v___x_2570_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2571_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2570_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
return v___x_2571_;
}
else
{
uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2572_ = 0;
v___x_2573_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = lean_array_get(v___x_2573_, v_alts_2563_, v___x_2574_);
lean_dec_ref(v_alts_2563_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_params_2576_; lean_object* v_code_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2628_; 
v_params_2576_ = lean_ctor_get(v___x_2575_, 1);
v_code_2577_ = lean_ctor_get(v___x_2575_, 2);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v___x_2575_, 0);
lean_dec(v_unused_2629_);
v___x_2579_ = v___x_2575_;
v_isShared_2580_ = v_isSharedCheck_2628_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_code_2577_);
lean_inc(v_params_2576_);
lean_dec(v___x_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2628_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2572_, v_params_2576_, v_a_2558_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v_fvarId_2585_; lean_object* v_binderName_2586_; lean_object* v_lctx_2587_; lean_object* v_nextIdx_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref_known(v___x_2581_, 1);
v___x_2582_ = lean_st_ref_take(v_a_2558_);
v___x_2583_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2584_ = lean_array_get(v___x_2583_, v_params_2576_, v___x_2574_);
lean_dec_ref(v_params_2576_);
v_fvarId_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_fvarId_2585_);
v_binderName_2586_ = lean_ctor_get(v___x_2584_, 1);
lean_inc(v_binderName_2586_);
lean_dec(v___x_2584_);
v_lctx_2587_ = lean_ctor_get(v___x_2582_, 0);
v_nextIdx_2588_ = lean_ctor_get(v___x_2582_, 1);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2590_ = v___x_2582_;
v_isShared_2591_ = v_isSharedCheck_2619_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_nextIdx_2588_);
lean_inc(v_lctx_2587_);
lean_dec(v___x_2582_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2619_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2592_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_discr_2562_);
v___x_2595_ = lean_mk_empty_array_with_capacity(v___x_2568_);
v___x_2596_ = lean_array_push(v___x_2595_, v___x_2594_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set_tag(v___x_2579_, 3);
lean_ctor_set(v___x_2579_, 2, v___x_2596_);
lean_ctor_set(v___x_2579_, 1, v___x_2593_);
lean_ctor_set(v___x_2579_, 0, v___x_2592_);
v___x_2598_ = v___x_2579_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2599_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 3, v___x_2598_);
lean_ctor_set(v___x_2565_, 2, v___x_2599_);
lean_ctor_set(v___x_2565_, 1, v_binderName_2586_);
lean_ctor_set(v___x_2565_, 0, v_fvarId_2585_);
v___x_2601_ = v___x_2565_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_fvarId_2585_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_binderName_2586_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2617_, 3, v___x_2598_);
v___x_2601_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2604_; 
lean_inc_ref(v___x_2601_);
v___x_2602_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2572_, v_lctx_2587_, v___x_2601_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2602_);
v___x_2604_ = v___x_2590_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_nextIdx_2588_);
v___x_2604_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_st_ref_set(v_a_2558_, v___x_2604_);
v___x_2606_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2577_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2615_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2601_);
lean_ctor_set(v___x_2611_, 1, v_a_2607_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_dec_ref(v___x_2601_);
return v___x_2606_;
}
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_del_object(v___x_2579_);
lean_dec_ref(v_code_2577_);
lean_dec_ref(v_params_2576_);
lean_del_object(v___x_2565_);
lean_dec(v_discr_2562_);
v_a_2620_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2581_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2581_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v___x_2575_);
lean_del_object(v___x_2565_);
lean_dec(v_discr_2562_);
v___x_2630_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2631_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2630_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
return v___x_2631_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2636_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2637_ = lean_unsigned_to_nat(2u);
v___x_2638_ = lean_unsigned_to_nat(284u);
v___x_2639_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2640_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2641_ = l_mkPanicMessageWithDecl(v___x_2640_, v___x_2639_, v___x_2638_, v___x_2637_, v___x_2636_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2646_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2647_ = lean_unsigned_to_nat(34u);
v___x_2648_ = lean_unsigned_to_nat(285u);
v___x_2649_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2650_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2651_ = l_mkPanicMessageWithDecl(v___x_2650_, v___x_2649_, v___x_2648_, v___x_2647_, v___x_2646_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_){
_start:
{
lean_object* v_discr_2659_; lean_object* v_alts_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2729_; 
v_discr_2659_ = lean_ctor_get(v_c_2652_, 2);
v_alts_2660_ = lean_ctor_get(v_c_2652_, 3);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_c_2652_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; lean_object* v_unused_2731_; 
v_unused_2730_ = lean_ctor_get(v_c_2652_, 1);
lean_dec(v_unused_2730_);
v_unused_2731_ = lean_ctor_get(v_c_2652_, 0);
lean_dec(v_unused_2731_);
v___x_2662_ = v_c_2652_;
v_isShared_2663_ = v_isSharedCheck_2729_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_alts_2660_);
lean_inc(v_discr_2659_);
lean_dec(v_c_2652_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2729_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2664_ = lean_array_get_size(v_alts_2660_);
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_dec_eq(v___x_2664_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_del_object(v___x_2662_);
lean_dec_ref(v_alts_2660_);
lean_dec(v_discr_2659_);
v___x_2667_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2668_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2667_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
return v___x_2668_;
}
else
{
uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2669_ = 0;
v___x_2670_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = lean_array_get(v___x_2670_, v_alts_2660_, v___x_2671_);
lean_dec_ref(v_alts_2660_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_params_2673_; lean_object* v_code_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2725_; 
v_params_2673_ = lean_ctor_get(v___x_2672_, 1);
v_code_2674_ = lean_ctor_get(v___x_2672_, 2);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; 
v_unused_2726_ = lean_ctor_get(v___x_2672_, 0);
lean_dec(v_unused_2726_);
v___x_2676_ = v___x_2672_;
v_isShared_2677_ = v_isSharedCheck_2725_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_code_2674_);
lean_inc(v_params_2673_);
lean_dec(v___x_2672_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2725_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2669_, v_params_2673_, v_a_2655_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v_fvarId_2682_; lean_object* v_binderName_2683_; lean_object* v_lctx_2684_; lean_object* v_nextIdx_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref_known(v___x_2678_, 1);
v___x_2679_ = lean_st_ref_take(v_a_2655_);
v___x_2680_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2681_ = lean_array_get(v___x_2680_, v_params_2673_, v___x_2671_);
lean_dec_ref(v_params_2673_);
v_fvarId_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_fvarId_2682_);
v_binderName_2683_ = lean_ctor_get(v___x_2681_, 1);
lean_inc(v_binderName_2683_);
lean_dec(v___x_2681_);
v_lctx_2684_ = lean_ctor_get(v___x_2679_, 0);
v_nextIdx_2685_ = lean_ctor_get(v___x_2679_, 1);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2687_ = v___x_2679_;
v_isShared_2688_ = v_isSharedCheck_2716_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_nextIdx_2685_);
lean_inc(v_lctx_2684_);
lean_dec(v___x_2679_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2716_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2689_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2691_, 0, v_discr_2659_);
v___x_2692_ = lean_mk_empty_array_with_capacity(v___x_2665_);
v___x_2693_ = lean_array_push(v___x_2692_, v___x_2691_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 3);
lean_ctor_set(v___x_2676_, 2, v___x_2693_);
lean_ctor_set(v___x_2676_, 1, v___x_2690_);
lean_ctor_set(v___x_2676_, 0, v___x_2689_);
v___x_2695_ = v___x_2676_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 3, v___x_2695_);
lean_ctor_set(v___x_2662_, 2, v___x_2696_);
lean_ctor_set(v___x_2662_, 1, v_binderName_2683_);
lean_ctor_set(v___x_2662_, 0, v_fvarId_2682_);
v___x_2698_ = v___x_2662_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_fvarId_2682_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_binderName_2683_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2714_, 3, v___x_2695_);
v___x_2698_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_inc_ref(v___x_2698_);
v___x_2699_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2669_, v_lctx_2684_, v___x_2698_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2699_);
v___x_2701_ = v___x_2687_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2699_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_nextIdx_2685_);
v___x_2701_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_st_ref_set(v_a_2655_, v___x_2701_);
v___x_2703_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2674_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2712_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2712_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2712_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2698_);
lean_ctor_set(v___x_2708_, 1, v_a_2704_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2708_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
else
{
lean_dec_ref(v___x_2698_);
return v___x_2703_;
}
}
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_del_object(v___x_2676_);
lean_dec_ref(v_code_2674_);
lean_dec_ref(v_params_2673_);
lean_del_object(v___x_2662_);
lean_dec(v_discr_2659_);
v_a_2717_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2678_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2678_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec(v___x_2672_);
lean_del_object(v___x_2662_);
lean_dec(v_discr_2659_);
v___x_2727_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2728_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2727_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
return v___x_2728_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2733_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2734_ = lean_unsigned_to_nat(2u);
v___x_2735_ = lean_unsigned_to_nat(273u);
v___x_2736_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2737_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2738_ = l_mkPanicMessageWithDecl(v___x_2737_, v___x_2736_, v___x_2735_, v___x_2734_, v___x_2733_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2743_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2744_ = lean_unsigned_to_nat(34u);
v___x_2745_ = lean_unsigned_to_nat(274u);
v___x_2746_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2747_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2748_ = l_mkPanicMessageWithDecl(v___x_2747_, v___x_2746_, v___x_2745_, v___x_2744_, v___x_2743_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_discr_2756_; lean_object* v_alts_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2826_; 
v_discr_2756_ = lean_ctor_get(v_c_2749_, 2);
v_alts_2757_ = lean_ctor_get(v_c_2749_, 3);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_c_2749_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; lean_object* v_unused_2828_; 
v_unused_2827_ = lean_ctor_get(v_c_2749_, 1);
lean_dec(v_unused_2827_);
v_unused_2828_ = lean_ctor_get(v_c_2749_, 0);
lean_dec(v_unused_2828_);
v___x_2759_ = v_c_2749_;
v_isShared_2760_ = v_isSharedCheck_2826_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_alts_2757_);
lean_inc(v_discr_2756_);
lean_dec(v_c_2749_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2826_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v___x_2761_ = lean_array_get_size(v_alts_2757_);
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_dec_eq(v___x_2761_, v___x_2762_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_del_object(v___x_2759_);
lean_dec_ref(v_alts_2757_);
lean_dec(v_discr_2756_);
v___x_2764_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2765_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2764_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
return v___x_2765_;
}
else
{
uint8_t v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2766_ = 0;
v___x_2767_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = lean_array_get(v___x_2767_, v_alts_2757_, v___x_2768_);
lean_dec_ref(v_alts_2757_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_params_2770_; lean_object* v_code_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2822_; 
v_params_2770_ = lean_ctor_get(v___x_2769_, 1);
v_code_2771_ = lean_ctor_get(v___x_2769_, 2);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2822_ == 0)
{
lean_object* v_unused_2823_; 
v_unused_2823_ = lean_ctor_get(v___x_2769_, 0);
lean_dec(v_unused_2823_);
v___x_2773_ = v___x_2769_;
v_isShared_2774_ = v_isSharedCheck_2822_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_code_2771_);
lean_inc(v_params_2770_);
lean_dec(v___x_2769_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2822_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2766_, v_params_2770_, v_a_2752_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v_fvarId_2779_; lean_object* v_binderName_2780_; lean_object* v_lctx_2781_; lean_object* v_nextIdx_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref_known(v___x_2775_, 1);
v___x_2776_ = lean_st_ref_take(v_a_2752_);
v___x_2777_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2778_ = lean_array_get(v___x_2777_, v_params_2770_, v___x_2768_);
lean_dec_ref(v_params_2770_);
v_fvarId_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_fvarId_2779_);
v_binderName_2780_ = lean_ctor_get(v___x_2778_, 1);
lean_inc(v_binderName_2780_);
lean_dec(v___x_2778_);
v_lctx_2781_ = lean_ctor_get(v___x_2776_, 0);
v_nextIdx_2782_ = lean_ctor_get(v___x_2776_, 1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2784_ = v___x_2776_;
v_isShared_2785_ = v_isSharedCheck_2813_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_nextIdx_2782_);
lean_inc(v_lctx_2781_);
lean_dec(v___x_2776_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2813_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2786_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_discr_2756_);
v___x_2789_ = lean_mk_empty_array_with_capacity(v___x_2762_);
v___x_2790_ = lean_array_push(v___x_2789_, v___x_2788_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 3);
lean_ctor_set(v___x_2773_, 2, v___x_2790_);
lean_ctor_set(v___x_2773_, 1, v___x_2787_);
lean_ctor_set(v___x_2773_, 0, v___x_2786_);
v___x_2792_ = v___x_2773_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 3, v___x_2792_);
lean_ctor_set(v___x_2759_, 2, v___x_2793_);
lean_ctor_set(v___x_2759_, 1, v_binderName_2780_);
lean_ctor_set(v___x_2759_, 0, v_fvarId_2779_);
v___x_2795_ = v___x_2759_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_fvarId_2779_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_binderName_2780_);
lean_ctor_set(v_reuseFailAlloc_2811_, 2, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2811_, 3, v___x_2792_);
v___x_2795_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
lean_inc_ref(v___x_2795_);
v___x_2796_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2766_, v_lctx_2781_, v___x_2795_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2796_);
v___x_2798_ = v___x_2784_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2810_, 1, v_nextIdx_2782_);
v___x_2798_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_st_ref_set(v_a_2752_, v___x_2798_);
v___x_2800_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2771_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2809_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2800_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2803_ = v___x_2800_;
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2800_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2809_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2795_);
lean_ctor_set(v___x_2805_, 1, v_a_2801_);
if (v_isShared_2804_ == 0)
{
lean_ctor_set(v___x_2803_, 0, v___x_2805_);
v___x_2807_ = v___x_2803_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
else
{
lean_dec_ref(v___x_2795_);
return v___x_2800_;
}
}
}
}
}
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_del_object(v___x_2773_);
lean_dec_ref(v_code_2771_);
lean_dec_ref(v_params_2770_);
lean_del_object(v___x_2759_);
lean_dec(v_discr_2756_);
v_a_2814_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2775_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2775_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v___x_2769_);
lean_del_object(v___x_2759_);
lean_dec(v_discr_2756_);
v___x_2824_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2825_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2824_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_);
return v___x_2825_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2830_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2831_ = lean_unsigned_to_nat(2u);
v___x_2832_ = lean_unsigned_to_nat(261u);
v___x_2833_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2834_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2835_ = l_mkPanicMessageWithDecl(v___x_2834_, v___x_2833_, v___x_2832_, v___x_2831_, v___x_2830_);
return v___x_2835_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2840_ = lean_unsigned_to_nat(34u);
v___x_2841_ = lean_unsigned_to_nat(262u);
v___x_2842_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2843_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2844_ = l_mkPanicMessageWithDecl(v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_, v___x_2839_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_discr_2852_; lean_object* v_alts_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2922_; 
v_discr_2852_ = lean_ctor_get(v_c_2845_, 2);
v_alts_2853_ = lean_ctor_get(v_c_2845_, 3);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_c_2845_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; lean_object* v_unused_2924_; 
v_unused_2923_ = lean_ctor_get(v_c_2845_, 1);
lean_dec(v_unused_2923_);
v_unused_2924_ = lean_ctor_get(v_c_2845_, 0);
lean_dec(v_unused_2924_);
v___x_2855_ = v_c_2845_;
v_isShared_2856_ = v_isSharedCheck_2922_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_alts_2853_);
lean_inc(v_discr_2852_);
lean_dec(v_c_2845_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2922_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = lean_array_get_size(v_alts_2853_);
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = lean_nat_dec_eq(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_del_object(v___x_2855_);
lean_dec_ref(v_alts_2853_);
lean_dec(v_discr_2852_);
v___x_2860_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2861_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2860_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2861_;
}
else
{
uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2862_ = 0;
v___x_2863_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2864_ = lean_unsigned_to_nat(0u);
v___x_2865_ = lean_array_get(v___x_2863_, v_alts_2853_, v___x_2864_);
lean_dec_ref(v_alts_2853_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_params_2866_; lean_object* v_code_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2918_; 
v_params_2866_ = lean_ctor_get(v___x_2865_, 1);
v_code_2867_ = lean_ctor_get(v___x_2865_, 2);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2865_, 0);
lean_dec(v_unused_2919_);
v___x_2869_ = v___x_2865_;
v_isShared_2870_ = v_isSharedCheck_2918_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_code_2867_);
lean_inc(v_params_2866_);
lean_dec(v___x_2865_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2918_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2862_, v_params_2866_, v_a_2848_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v_fvarId_2875_; lean_object* v_binderName_2876_; lean_object* v_lctx_2877_; lean_object* v_nextIdx_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2909_; 
lean_dec_ref_known(v___x_2871_, 1);
v___x_2872_ = lean_st_ref_take(v_a_2848_);
v___x_2873_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2874_ = lean_array_get(v___x_2873_, v_params_2866_, v___x_2864_);
lean_dec_ref(v_params_2866_);
v_fvarId_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_fvarId_2875_);
v_binderName_2876_ = lean_ctor_get(v___x_2874_, 1);
lean_inc(v_binderName_2876_);
lean_dec(v___x_2874_);
v_lctx_2877_ = lean_ctor_get(v___x_2872_, 0);
v_nextIdx_2878_ = lean_ctor_get(v___x_2872_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2880_ = v___x_2872_;
v_isShared_2881_ = v_isSharedCheck_2909_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_nextIdx_2878_);
lean_inc(v_lctx_2877_);
lean_dec(v___x_2872_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2909_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2882_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2884_, 0, v_discr_2852_);
v___x_2885_ = lean_mk_empty_array_with_capacity(v___x_2858_);
v___x_2886_ = lean_array_push(v___x_2885_, v___x_2884_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 3);
lean_ctor_set(v___x_2869_, 2, v___x_2886_);
lean_ctor_set(v___x_2869_, 1, v___x_2883_);
lean_ctor_set(v___x_2869_, 0, v___x_2882_);
v___x_2888_ = v___x_2869_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 3, v___x_2888_);
lean_ctor_set(v___x_2855_, 2, v___x_2889_);
lean_ctor_set(v___x_2855_, 1, v_binderName_2876_);
lean_ctor_set(v___x_2855_, 0, v_fvarId_2875_);
v___x_2891_ = v___x_2855_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_fvarId_2875_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_binderName_2876_);
lean_ctor_set(v_reuseFailAlloc_2907_, 2, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2907_, 3, v___x_2888_);
v___x_2891_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
lean_inc_ref(v___x_2891_);
v___x_2892_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2862_, v_lctx_2877_, v___x_2891_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2892_);
v___x_2894_ = v___x_2880_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_nextIdx_2878_);
v___x_2894_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_st_ref_set(v_a_2848_, v___x_2894_);
v___x_2896_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2867_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2905_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2905_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2891_);
lean_ctor_set(v___x_2901_, 1, v_a_2897_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2901_);
v___x_2903_ = v___x_2899_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_dec_ref(v___x_2891_);
return v___x_2896_;
}
}
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_del_object(v___x_2869_);
lean_dec_ref(v_code_2867_);
lean_dec_ref(v_params_2866_);
lean_del_object(v___x_2855_);
lean_dec(v_discr_2852_);
v_a_2910_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2871_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2871_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec(v___x_2865_);
lean_del_object(v___x_2855_);
lean_dec(v_discr_2852_);
v___x_2920_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2921_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2920_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
return v___x_2921_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2926_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2927_ = lean_unsigned_to_nat(2u);
v___x_2928_ = lean_unsigned_to_nat(249u);
v___x_2929_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2930_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2931_ = l_mkPanicMessageWithDecl(v___x_2930_, v___x_2929_, v___x_2928_, v___x_2927_, v___x_2926_);
return v___x_2931_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2936_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2937_ = lean_unsigned_to_nat(34u);
v___x_2938_ = lean_unsigned_to_nat(250u);
v___x_2939_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2940_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2941_ = l_mkPanicMessageWithDecl(v___x_2940_, v___x_2939_, v___x_2938_, v___x_2937_, v___x_2936_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_){
_start:
{
lean_object* v_discr_2949_; lean_object* v_alts_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3019_; 
v_discr_2949_ = lean_ctor_get(v_c_2942_, 2);
v_alts_2950_ = lean_ctor_get(v_c_2942_, 3);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_c_2942_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; lean_object* v_unused_3021_; 
v_unused_3020_ = lean_ctor_get(v_c_2942_, 1);
lean_dec(v_unused_3020_);
v_unused_3021_ = lean_ctor_get(v_c_2942_, 0);
lean_dec(v_unused_3021_);
v___x_2952_ = v_c_2942_;
v_isShared_2953_ = v_isSharedCheck_3019_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_alts_2950_);
lean_inc(v_discr_2949_);
lean_dec(v_c_2942_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3019_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v___x_2954_ = lean_array_get_size(v_alts_2950_);
v___x_2955_ = lean_unsigned_to_nat(1u);
v___x_2956_ = lean_nat_dec_eq(v___x_2954_, v___x_2955_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
lean_del_object(v___x_2952_);
lean_dec_ref(v_alts_2950_);
lean_dec(v_discr_2949_);
v___x_2957_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2958_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2957_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_2958_;
}
else
{
uint8_t v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2959_ = 0;
v___x_2960_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = lean_array_get(v___x_2960_, v_alts_2950_, v___x_2961_);
lean_dec_ref(v_alts_2950_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_params_2963_; lean_object* v_code_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3015_; 
v_params_2963_ = lean_ctor_get(v___x_2962_, 1);
v_code_2964_ = lean_ctor_get(v___x_2962_, 2);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_2962_, 0);
lean_dec(v_unused_3016_);
v___x_2966_ = v___x_2962_;
v_isShared_2967_ = v_isSharedCheck_3015_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_code_2964_);
lean_inc(v_params_2963_);
lean_dec(v___x_2962_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3015_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2959_, v_params_2963_, v_a_2945_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v_fvarId_2972_; lean_object* v_binderName_2973_; lean_object* v_lctx_2974_; lean_object* v_nextIdx_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref_known(v___x_2968_, 1);
v___x_2969_ = lean_st_ref_take(v_a_2945_);
v___x_2970_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2971_ = lean_array_get(v___x_2970_, v_params_2963_, v___x_2961_);
lean_dec_ref(v_params_2963_);
v_fvarId_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_fvarId_2972_);
v_binderName_2973_ = lean_ctor_get(v___x_2971_, 1);
lean_inc(v_binderName_2973_);
lean_dec(v___x_2971_);
v_lctx_2974_ = lean_ctor_get(v___x_2969_, 0);
v_nextIdx_2975_ = lean_ctor_get(v___x_2969_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_2977_ = v___x_2969_;
v_isShared_2978_ = v_isSharedCheck_3006_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_nextIdx_2975_);
lean_inc(v_lctx_2974_);
lean_dec(v___x_2969_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3006_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2979_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_discr_2949_);
v___x_2982_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2983_ = lean_array_push(v___x_2982_, v___x_2981_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set_tag(v___x_2966_, 3);
lean_ctor_set(v___x_2966_, 2, v___x_2983_);
lean_ctor_set(v___x_2966_, 1, v___x_2980_);
lean_ctor_set(v___x_2966_, 0, v___x_2979_);
v___x_2985_ = v___x_2966_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2986_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 3, v___x_2985_);
lean_ctor_set(v___x_2952_, 2, v___x_2986_);
lean_ctor_set(v___x_2952_, 1, v_binderName_2973_);
lean_ctor_set(v___x_2952_, 0, v_fvarId_2972_);
v___x_2988_ = v___x_2952_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_fvarId_2972_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_binderName_2973_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v___x_2985_);
v___x_2988_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
lean_inc_ref(v___x_2988_);
v___x_2989_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2959_, v_lctx_2974_, v___x_2988_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 0, v___x_2989_);
v___x_2991_ = v___x_2977_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_nextIdx_2975_);
v___x_2991_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_st_ref_set(v_a_2945_, v___x_2991_);
v___x_2993_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2964_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3002_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3002_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2988_);
lean_ctor_set(v___x_2998_, 1, v_a_2994_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v___x_2998_);
v___x_3000_ = v___x_2996_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
lean_dec_ref(v___x_2988_);
return v___x_2993_;
}
}
}
}
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2966_);
lean_dec_ref(v_code_2964_);
lean_dec_ref(v_params_2963_);
lean_del_object(v___x_2952_);
lean_dec(v_discr_2949_);
v_a_3007_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2968_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2968_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec(v___x_2962_);
lean_del_object(v___x_2952_);
lean_dec(v_discr_2949_);
v___x_3017_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_3018_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3017_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
return v___x_3018_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3023_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_3024_ = lean_unsigned_to_nat(2u);
v___x_3025_ = lean_unsigned_to_nat(238u);
v___x_3026_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3027_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_3028_ = l_mkPanicMessageWithDecl(v___x_3027_, v___x_3026_, v___x_3025_, v___x_3024_, v___x_3023_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3030_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_3031_ = lean_unsigned_to_nat(34u);
v___x_3032_ = lean_unsigned_to_nat(239u);
v___x_3033_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3034_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_3035_ = l_mkPanicMessageWithDecl(v___x_3034_, v___x_3033_, v___x_3032_, v___x_3031_, v___x_3030_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_3036_, lean_object* v_uintName_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_){
_start:
{
lean_object* v_discr_3044_; lean_object* v_alts_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3115_; 
v_discr_3044_ = lean_ctor_get(v_c_3036_, 2);
v_alts_3045_ = lean_ctor_get(v_c_3036_, 3);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_c_3036_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; lean_object* v_unused_3117_; 
v_unused_3116_ = lean_ctor_get(v_c_3036_, 1);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_c_3036_, 0);
lean_dec(v_unused_3117_);
v___x_3047_ = v_c_3036_;
v_isShared_3048_ = v_isSharedCheck_3115_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_alts_3045_);
lean_inc(v_discr_3044_);
lean_dec(v_c_3036_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3115_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v___x_3049_ = lean_array_get_size(v_alts_3045_);
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_dec_eq(v___x_3049_, v___x_3050_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_del_object(v___x_3047_);
lean_dec_ref(v_alts_3045_);
lean_dec(v_discr_3044_);
lean_dec(v_uintName_3037_);
v___x_3052_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_3053_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3052_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
return v___x_3053_;
}
else
{
uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3054_ = 0;
v___x_3055_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = lean_array_get(v___x_3055_, v_alts_3045_, v___x_3056_);
lean_dec_ref(v_alts_3045_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_params_3058_; lean_object* v_code_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3111_; 
v_params_3058_ = lean_ctor_get(v___x_3057_, 1);
v_code_3059_ = lean_ctor_get(v___x_3057_, 2);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3057_, 0);
lean_dec(v_unused_3112_);
v___x_3061_ = v___x_3057_;
v_isShared_3062_ = v_isSharedCheck_3111_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_code_3059_);
lean_inc(v_params_3058_);
lean_dec(v___x_3057_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3111_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3054_, v_params_3058_, v_a_3040_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_fvarId_3067_; lean_object* v_binderName_3068_; lean_object* v_lctx_3069_; lean_object* v_nextIdx_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref_known(v___x_3063_, 1);
v___x_3064_ = lean_st_ref_take(v_a_3040_);
v___x_3065_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3066_ = lean_array_get(v___x_3065_, v_params_3058_, v___x_3056_);
lean_dec_ref(v_params_3058_);
v_fvarId_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_fvarId_3067_);
v_binderName_3068_ = lean_ctor_get(v___x_3066_, 1);
lean_inc(v_binderName_3068_);
lean_dec(v___x_3066_);
v_lctx_3069_ = lean_ctor_get(v___x_3064_, 0);
v_nextIdx_3070_ = lean_ctor_get(v___x_3064_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3072_ = v___x_3064_;
v_isShared_3073_ = v_isSharedCheck_3102_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_nextIdx_3070_);
lean_inc(v_lctx_3069_);
lean_dec(v___x_3064_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3102_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3074_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3));
v___x_3075_ = l_Lean_Name_str___override(v_uintName_3037_, v___x_3074_);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3077_, 0, v_discr_3044_);
v___x_3078_ = lean_mk_empty_array_with_capacity(v___x_3050_);
v___x_3079_ = lean_array_push(v___x_3078_, v___x_3077_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 3);
lean_ctor_set(v___x_3061_, 2, v___x_3079_);
lean_ctor_set(v___x_3061_, 1, v___x_3076_);
lean_ctor_set(v___x_3061_, 0, v___x_3075_);
v___x_3081_ = v___x_3061_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
v___x_3082_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 3, v___x_3081_);
lean_ctor_set(v___x_3047_, 2, v___x_3082_);
lean_ctor_set(v___x_3047_, 1, v_binderName_3068_);
lean_ctor_set(v___x_3047_, 0, v_fvarId_3067_);
v___x_3084_ = v___x_3047_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_fvarId_3067_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_binderName_3068_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3100_, 3, v___x_3081_);
v___x_3084_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
lean_inc_ref(v___x_3084_);
v___x_3085_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3054_, v_lctx_3069_, v___x_3084_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v___x_3085_);
v___x_3087_ = v___x_3072_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_nextIdx_3070_);
v___x_3087_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_st_ref_set(v_a_3040_, v___x_3087_);
v___x_3089_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3059_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3084_);
lean_ctor_set(v___x_3094_, 1, v_a_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_dec_ref(v___x_3084_);
return v___x_3089_;
}
}
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_del_object(v___x_3061_);
lean_dec_ref(v_code_3059_);
lean_dec_ref(v_params_3058_);
lean_del_object(v___x_3047_);
lean_dec(v_discr_3044_);
lean_dec(v_uintName_3037_);
v_a_3103_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3063_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3063_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v___x_3057_);
lean_del_object(v___x_3047_);
lean_dec(v_discr_3044_);
lean_dec(v_uintName_3037_);
v___x_3113_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4);
v___x_3114_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3113_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
return v___x_3114_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3120_ = l_Lean_mkConst(v___x_3119_, v___x_3118_);
return v___x_3120_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3129_ = l_Lean_mkConst(v___x_3128_, v___x_3127_);
return v___x_3129_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_box(0);
v___x_3138_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3139_ = l_Lean_mkConst(v___x_3138_, v___x_3137_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_3164_, size_t v_sz_3165_, size_t v_i_3166_, lean_object* v_bs_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_usize_dec_lt(v_i_3166_, v_sz_3165_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_dec(v___x_3164_);
v___x_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_bs_3167_);
return v___x_3175_;
}
else
{
lean_object* v_v_3176_; lean_object* v___x_3177_; lean_object* v_bs_x27_3178_; lean_object* v_a_3180_; 
v_v_3176_ = lean_array_uget(v_bs_3167_, v_i_3166_);
v___x_3177_ = lean_unsigned_to_nat(0u);
v_bs_x27_3178_ = lean_array_uset(v_bs_3167_, v_i_3166_, v___x_3177_);
if (lean_obj_tag(v_v_3176_) == 0)
{
lean_object* v_ctorName_3185_; lean_object* v_params_3186_; lean_object* v_code_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3314_; 
v_ctorName_3185_ = lean_ctor_get(v_v_3176_, 0);
v_params_3186_ = lean_ctor_get(v_v_3176_, 1);
v_code_3187_ = lean_ctor_get(v_v_3176_, 2);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_v_3176_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3189_ = v_v_3176_;
v_isShared_3190_ = v_isSharedCheck_3314_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_code_3187_);
lean_inc(v_params_3186_);
lean_inc(v_ctorName_3185_);
lean_dec(v_v_3176_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3314_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
uint8_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3191_ = 0;
v___x_3192_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3193_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3191_, v_params_3186_, v___y_3170_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
lean_dec_ref_known(v___x_3193_, 1);
v___x_3194_ = lean_box(0);
v___x_3195_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3196_ = lean_array_get(v___x_3192_, v_params_3186_, v___x_3177_);
lean_dec_ref(v_params_3186_);
v___x_3197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_3198_ = lean_name_eq(v_ctorName_3185_, v___x_3197_);
lean_dec(v_ctorName_3185_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v_fvarId_3200_; lean_object* v_binderName_3201_; lean_object* v_lctx_3202_; lean_object* v_nextIdx_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3234_; 
v___x_3199_ = lean_st_ref_take(v___y_3170_);
v_fvarId_3200_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_fvarId_3200_);
v_binderName_3201_ = lean_ctor_get(v___x_3196_, 1);
lean_inc(v_binderName_3201_);
lean_dec(v___x_3196_);
v_lctx_3202_ = lean_ctor_get(v___x_3199_, 0);
v_nextIdx_3203_ = lean_ctor_get(v___x_3199_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3205_ = v___x_3199_;
v_isShared_3206_ = v_isSharedCheck_3234_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_nextIdx_3203_);
lean_inc(v_lctx_3202_);
lean_dec(v___x_3199_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3234_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_3208_ = lean_unsigned_to_nat(1u);
v___x_3209_ = lean_mk_empty_array_with_capacity(v___x_3208_);
lean_inc(v___x_3164_);
v___x_3210_ = lean_array_push(v___x_3209_, v___x_3164_);
v___x_3211_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3207_);
lean_ctor_set(v___x_3211_, 1, v___x_3194_);
lean_ctor_set(v___x_3211_, 2, v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3212_, 0, v_fvarId_3200_);
lean_ctor_set(v___x_3212_, 1, v_binderName_3201_);
lean_ctor_set(v___x_3212_, 2, v___x_3195_);
lean_ctor_set(v___x_3212_, 3, v___x_3211_);
lean_inc_ref(v___x_3212_);
v___x_3213_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3191_, v_lctx_3202_, v___x_3212_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3213_);
v___x_3215_ = v___x_3205_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_nextIdx_3203_);
v___x_3215_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = lean_st_ref_set(v___y_3170_, v___x_3215_);
v___x_3217_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3187_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_3220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3212_);
lean_ctor_set(v___x_3221_, 1, v_a_3218_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 2, v___x_3221_);
lean_ctor_set(v___x_3189_, 1, v___x_3220_);
lean_ctor_set(v___x_3189_, 0, v___x_3219_);
v___x_3223_ = v___x_3189_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
v_a_3180_ = v___x_3223_;
goto v___jp_3179_;
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref_known(v___x_3212_, 4);
lean_del_object(v___x_3189_);
lean_dec_ref(v_bs_x27_3178_);
lean_dec(v___x_3164_);
v_a_3225_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3217_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3217_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3235_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_3236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_mk_empty_array_with_capacity(v___x_3237_);
lean_inc(v___x_3164_);
v___x_3239_ = lean_array_push(v___x_3238_, v___x_3164_);
v___x_3240_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3236_);
lean_ctor_set(v___x_3240_, 1, v___x_3194_);
lean_ctor_set(v___x_3240_, 2, v___x_3239_);
v___x_3241_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3191_, v___x_3235_, v___x_3195_, v___x_3240_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3));
v___x_3245_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3191_, v___x_3243_, v___x_3195_, v___x_3244_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v_fvarId_3247_; lean_object* v_fvarId_3248_; lean_object* v___x_3249_; lean_object* v_fvarId_3250_; lean_object* v_binderName_3251_; lean_object* v_lctx_3252_; lean_object* v_nextIdx_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3289_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
v_fvarId_3247_ = lean_ctor_get(v_a_3242_, 0);
v_fvarId_3248_ = lean_ctor_get(v_a_3246_, 0);
v___x_3249_ = lean_st_ref_take(v___y_3170_);
v_fvarId_3250_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_fvarId_3250_);
v_binderName_3251_ = lean_ctor_get(v___x_3196_, 1);
lean_inc(v_binderName_3251_);
lean_dec(v___x_3196_);
v_lctx_3252_ = lean_ctor_get(v___x_3249_, 0);
v_nextIdx_3253_ = lean_ctor_get(v___x_3249_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3255_ = v___x_3249_;
v_isShared_3256_ = v_isSharedCheck_3289_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_nextIdx_3253_);
lean_inc(v_lctx_3252_);
lean_dec(v___x_3249_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3289_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5));
lean_inc(v_fvarId_3247_);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_fvarId_3247_);
lean_inc(v_fvarId_3248_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_fvarId_3248_);
v___x_3260_ = lean_unsigned_to_nat(2u);
v___x_3261_ = lean_mk_empty_array_with_capacity(v___x_3260_);
v___x_3262_ = lean_array_push(v___x_3261_, v___x_3258_);
v___x_3263_ = lean_array_push(v___x_3262_, v___x_3259_);
v___x_3264_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3257_);
lean_ctor_set(v___x_3264_, 1, v___x_3194_);
lean_ctor_set(v___x_3264_, 2, v___x_3263_);
v___x_3265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3265_, 0, v_fvarId_3250_);
lean_ctor_set(v___x_3265_, 1, v_binderName_3251_);
lean_ctor_set(v___x_3265_, 2, v___x_3195_);
lean_ctor_set(v___x_3265_, 3, v___x_3264_);
lean_inc_ref(v___x_3265_);
v___x_3266_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3191_, v_lctx_3252_, v___x_3265_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3266_);
v___x_3268_ = v___x_3255_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_nextIdx_3253_);
v___x_3268_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = lean_st_ref_set(v___y_3170_, v___x_3268_);
v___x_3270_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3187_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3265_);
lean_ctor_set(v___x_3274_, 1, v_a_3271_);
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v_a_3246_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3242_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 2, v___x_3276_);
lean_ctor_set(v___x_3189_, 1, v___x_3273_);
lean_ctor_set(v___x_3189_, 0, v___x_3272_);
v___x_3278_ = v___x_3189_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
v_a_3180_ = v___x_3278_;
goto v___jp_3179_;
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref_known(v___x_3265_, 4);
lean_dec(v_a_3246_);
lean_dec(v_a_3242_);
lean_del_object(v___x_3189_);
lean_dec_ref(v_bs_x27_3178_);
lean_dec(v___x_3164_);
v_a_3280_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3270_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3270_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_a_3242_);
lean_dec(v___x_3196_);
lean_del_object(v___x_3189_);
lean_dec_ref(v_code_3187_);
lean_dec_ref(v_bs_x27_3178_);
lean_dec(v___x_3164_);
v_a_3290_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3245_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3245_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v___x_3196_);
lean_del_object(v___x_3189_);
lean_dec_ref(v_code_3187_);
lean_dec_ref(v_bs_x27_3178_);
lean_dec(v___x_3164_);
v_a_3298_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3241_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3241_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_del_object(v___x_3189_);
lean_dec_ref(v_code_3187_);
lean_dec_ref(v_params_3186_);
lean_dec(v_ctorName_3185_);
lean_dec_ref(v_bs_x27_3178_);
lean_dec(v___x_3164_);
v_a_3306_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3193_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3193_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
}
else
{
lean_object* v_code_3315_; lean_object* v___x_3316_; 
v_code_3315_ = lean_ctor_get(v_v_3176_, 0);
lean_inc_ref(v_code_3315_);
v___x_3316_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3315_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3176_, v_a_3317_);
v_a_3180_ = v___x_3318_;
goto v___jp_3179_;
}
else
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3326_; 
lean_dec_ref_known(v_v_3176_, 1);
lean_dec_ref(v_bs_x27_3178_);
lean_dec(v___x_3164_);
v_a_3319_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3326_ == 0)
{
v___x_3321_ = v___x_3316_;
v_isShared_3322_ = v_isSharedCheck_3326_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3316_);
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
v___jp_3179_:
{
size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((size_t)1ULL);
v___x_3182_ = lean_usize_add(v_i_3166_, v___x_3181_);
v___x_3183_ = lean_array_uset(v_bs_x27_3178_, v_i_3166_, v_a_3180_);
v_i_3166_ = v___x_3182_;
v_bs_3167_ = v___x_3183_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_resultType_3334_; lean_object* v_discr_3335_; lean_object* v_alts_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3433_; 
v_resultType_3334_ = lean_ctor_get(v_c_3327_, 1);
v_discr_3335_ = lean_ctor_get(v_c_3327_, 2);
v_alts_3336_ = lean_ctor_get(v_c_3327_, 3);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_c_3327_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v_c_3327_, 0);
lean_dec(v_unused_3434_);
v___x_3338_ = v_c_3327_;
v_isShared_3339_ = v_isSharedCheck_3433_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_alts_3336_);
lean_inc(v_discr_3335_);
lean_inc(v_resultType_3334_);
lean_dec(v_c_3327_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3433_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3334_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = 0;
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3345_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3346_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_3347_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3342_, v___x_3345_, v___x_3344_, v___x_3346_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v_fvarId_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v_fvarId_3349_ = lean_ctor_get(v_a_3348_, 0);
v___x_3350_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3351_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3352_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3349_);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_fvarId_3349_);
v___x_3354_ = lean_unsigned_to_nat(1u);
v___x_3355_ = lean_mk_empty_array_with_capacity(v___x_3354_);
v___x_3356_ = lean_array_push(v___x_3355_, v___x_3353_);
v___x_3357_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3352_);
lean_ctor_set(v___x_3357_, 1, v___x_3343_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
v___x_3358_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3342_, v___x_3350_, v___x_3351_, v___x_3357_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v_fvarId_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_fvarId_3360_ = lean_ctor_get(v_a_3359_, 0);
v___x_3361_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3362_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3363_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5);
v___x_3364_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_discr_3335_);
lean_inc(v_fvarId_3360_);
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_fvarId_3360_);
v___x_3367_ = lean_unsigned_to_nat(2u);
v___x_3368_ = lean_mk_empty_array_with_capacity(v___x_3367_);
lean_inc_ref(v___x_3365_);
v___x_3369_ = lean_array_push(v___x_3368_, v___x_3365_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3366_);
v___x_3371_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3364_);
lean_ctor_set(v___x_3371_, 1, v___x_3343_);
lean_ctor_set(v___x_3371_, 2, v___x_3370_);
v___x_3372_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3342_, v___x_3361_, v___x_3363_, v___x_3371_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; size_t v_sz_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v_sz_3374_ = lean_array_size(v_alts_3336_);
v___x_3375_ = ((size_t)0ULL);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3365_, v_sz_3374_, v___x_3375_, v_alts_3336_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3392_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3392_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3392_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_fvarId_3381_; lean_object* v___x_3383_; 
v_fvarId_3381_ = lean_ctor_get(v_a_3373_, 0);
lean_inc(v_fvarId_3381_);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 3, v_a_3377_);
lean_ctor_set(v___x_3338_, 2, v_fvarId_3381_);
lean_ctor_set(v___x_3338_, 1, v_a_3341_);
lean_ctor_set(v___x_3338_, 0, v___x_3362_);
v___x_3383_ = v___x_3338_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_a_3341_);
lean_ctor_set(v_reuseFailAlloc_3391_, 2, v_fvarId_3381_);
lean_ctor_set(v_reuseFailAlloc_3391_, 3, v_a_3377_);
v___x_3383_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3384_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_a_3373_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3359_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_a_3348_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3387_);
v___x_3389_ = v___x_3379_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3387_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v_a_3373_);
lean_dec(v_a_3359_);
lean_dec(v_a_3348_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3338_);
v_a_3393_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3376_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3376_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec_ref_known(v___x_3365_, 1);
lean_dec(v_a_3359_);
lean_dec(v_a_3348_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3338_);
lean_dec_ref(v_alts_3336_);
v_a_3401_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3372_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3372_);
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
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_a_3348_);
lean_dec(v_a_3341_);
lean_del_object(v___x_3338_);
lean_dec_ref(v_alts_3336_);
lean_dec(v_discr_3335_);
v_a_3409_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3358_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3358_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_a_3341_);
lean_del_object(v___x_3338_);
lean_dec_ref(v_alts_3336_);
lean_dec(v_discr_3335_);
v_a_3417_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3347_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3347_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3432_; 
lean_del_object(v___x_3338_);
lean_dec_ref(v_alts_3336_);
lean_dec(v_discr_3335_);
v_a_3425_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3427_ = v___x_3340_;
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v___x_3340_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3432_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3444_, size_t v_sz_3445_, size_t v_i_3446_, lean_object* v_bs_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
uint8_t v___x_3454_; 
v___x_3454_ = lean_usize_dec_lt(v_i_3446_, v_sz_3445_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; 
lean_dec(v___x_3444_);
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_bs_3447_);
return v___x_3455_;
}
else
{
lean_object* v_v_3456_; lean_object* v___x_3457_; lean_object* v_bs_x27_3458_; lean_object* v_a_3460_; 
v_v_3456_ = lean_array_uget(v_bs_3447_, v_i_3446_);
v___x_3457_ = lean_unsigned_to_nat(0u);
v_bs_x27_3458_ = lean_array_uset(v_bs_3447_, v_i_3446_, v___x_3457_);
if (lean_obj_tag(v_v_3456_) == 0)
{
lean_object* v_ctorName_3465_; lean_object* v_params_3466_; lean_object* v_code_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3554_; 
v_ctorName_3465_ = lean_ctor_get(v_v_3456_, 0);
v_params_3466_ = lean_ctor_get(v_v_3456_, 1);
v_code_3467_ = lean_ctor_get(v_v_3456_, 2);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_v_3456_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3469_ = v_v_3456_;
v_isShared_3470_ = v_isSharedCheck_3554_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_code_3467_);
lean_inc(v_params_3466_);
lean_inc(v_ctorName_3465_);
lean_dec(v_v_3456_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3554_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
uint8_t v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = 0;
v___x_3472_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3471_, v_params_3466_, v___y_3450_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3473_; uint8_t v___x_3474_; 
lean_dec_ref_known(v___x_3472_, 1);
v___x_3473_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_3474_ = lean_name_eq(v_ctorName_3465_, v___x_3473_);
lean_dec(v_ctorName_3465_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref(v_params_3466_);
v___x_3475_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3467_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 2, v_a_3476_);
lean_ctor_set(v___x_3469_, 1, v___x_3478_);
lean_ctor_set(v___x_3469_, 0, v___x_3477_);
v___x_3480_ = v___x_3469_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v_a_3476_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
v_a_3460_ = v___x_3480_;
goto v___jp_3459_;
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_del_object(v___x_3469_);
lean_dec_ref(v_bs_x27_3458_);
lean_dec(v___x_3444_);
v_a_3482_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3475_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3475_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3490_ = lean_box(0);
v___x_3491_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3492_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3));
v___x_3495_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3471_, v___x_3493_, v___x_3491_, v___x_3494_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_fvarId_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v_fvarId_3500_; lean_object* v_binderName_3501_; lean_object* v_lctx_3502_; lean_object* v_nextIdx_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3537_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v_fvarId_3497_ = lean_ctor_get(v_a_3496_, 0);
v___x_3498_ = lean_st_ref_take(v___y_3450_);
v___x_3499_ = lean_array_get(v___x_3492_, v_params_3466_, v___x_3457_);
lean_dec_ref(v_params_3466_);
v_fvarId_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_fvarId_3500_);
v_binderName_3501_ = lean_ctor_get(v___x_3499_, 1);
lean_inc(v_binderName_3501_);
lean_dec(v___x_3499_);
v_lctx_3502_ = lean_ctor_get(v___x_3498_, 0);
v_nextIdx_3503_ = lean_ctor_get(v___x_3498_, 1);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3505_ = v___x_3498_;
v_isShared_3506_ = v_isSharedCheck_3537_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_nextIdx_3503_);
lean_inc(v_lctx_3502_);
lean_dec(v___x_3498_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3537_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5));
lean_inc(v_fvarId_3497_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_fvarId_3497_);
v___x_3509_ = lean_unsigned_to_nat(2u);
v___x_3510_ = lean_mk_empty_array_with_capacity(v___x_3509_);
lean_inc(v___x_3444_);
v___x_3511_ = lean_array_push(v___x_3510_, v___x_3444_);
v___x_3512_ = lean_array_push(v___x_3511_, v___x_3508_);
v___x_3513_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3507_);
lean_ctor_set(v___x_3513_, 1, v___x_3490_);
lean_ctor_set(v___x_3513_, 2, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3514_, 0, v_fvarId_3500_);
lean_ctor_set(v___x_3514_, 1, v_binderName_3501_);
lean_ctor_set(v___x_3514_, 2, v___x_3491_);
lean_ctor_set(v___x_3514_, 3, v___x_3513_);
lean_inc_ref(v___x_3514_);
v___x_3515_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3471_, v_lctx_3502_, v___x_3514_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3515_);
v___x_3517_ = v___x_3505_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3515_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_nextIdx_3503_);
v___x_3517_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_st_ref_set(v___y_3450_, v___x_3517_);
v___x_3519_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3467_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___x_3521_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_3522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3514_);
lean_ctor_set(v___x_3523_, 1, v_a_3520_);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v_a_3496_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 2, v___x_3524_);
lean_ctor_set(v___x_3469_, 1, v___x_3522_);
lean_ctor_set(v___x_3469_, 0, v___x_3521_);
v___x_3526_ = v___x_3469_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
v_a_3460_ = v___x_3526_;
goto v___jp_3459_;
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref_known(v___x_3514_, 4);
lean_dec(v_a_3496_);
lean_del_object(v___x_3469_);
lean_dec_ref(v_bs_x27_3458_);
lean_dec(v___x_3444_);
v_a_3528_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3519_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3519_);
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
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_del_object(v___x_3469_);
lean_dec_ref(v_code_3467_);
lean_dec_ref(v_params_3466_);
lean_dec_ref(v_bs_x27_3458_);
lean_dec(v___x_3444_);
v_a_3538_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3495_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3495_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3469_);
lean_dec_ref(v_code_3467_);
lean_dec_ref(v_params_3466_);
lean_dec(v_ctorName_3465_);
lean_dec_ref(v_bs_x27_3458_);
lean_dec(v___x_3444_);
v_a_3546_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3472_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3472_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
else
{
lean_object* v_code_3555_; lean_object* v___x_3556_; 
v_code_3555_ = lean_ctor_get(v_v_3456_, 0);
lean_inc_ref(v_code_3555_);
v___x_3556_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3555_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3558_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
lean_inc(v_a_3557_);
lean_dec_ref_known(v___x_3556_, 1);
v___x_3558_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3456_, v_a_3557_);
v_a_3460_ = v___x_3558_;
goto v___jp_3459_;
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref_known(v_v_3456_, 1);
lean_dec_ref(v_bs_x27_3458_);
lean_dec(v___x_3444_);
v_a_3559_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3556_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3556_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
v___jp_3459_:
{
size_t v___x_3461_; size_t v___x_3462_; lean_object* v___x_3463_; 
v___x_3461_ = ((size_t)1ULL);
v___x_3462_ = lean_usize_add(v_i_3446_, v___x_3461_);
v___x_3463_ = lean_array_uset(v_bs_x27_3458_, v_i_3446_, v_a_3460_);
v_i_3446_ = v___x_3462_;
v_bs_3447_ = v___x_3463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v_resultType_3574_; lean_object* v_discr_3575_; lean_object* v_alts_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3653_; 
v_resultType_3574_ = lean_ctor_get(v_c_3567_, 1);
v_discr_3575_ = lean_ctor_get(v_c_3567_, 2);
v_alts_3576_ = lean_ctor_get(v_c_3567_, 3);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_c_3567_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v_c_3567_, 0);
lean_dec(v_unused_3654_);
v___x_3578_ = v_c_3567_;
v_isShared_3579_ = v_isSharedCheck_3653_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_alts_3576_);
lean_inc(v_discr_3575_);
lean_inc(v_resultType_3574_);
lean_dec(v_c_3567_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3653_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3574_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
v___x_3582_ = 0;
v___x_3583_ = lean_box(0);
v___x_3584_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3585_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3586_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_3587_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3582_, v___x_3585_, v___x_3584_, v___x_3586_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v_fvarId_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref_known(v___x_3587_, 1);
v_fvarId_3589_ = lean_ctor_get(v_a_3588_, 0);
v___x_3590_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3591_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3592_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5);
v___x_3593_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7));
v___x_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3594_, 0, v_discr_3575_);
lean_inc(v_fvarId_3589_);
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_fvarId_3589_);
v___x_3596_ = lean_unsigned_to_nat(2u);
v___x_3597_ = lean_mk_empty_array_with_capacity(v___x_3596_);
lean_inc_ref(v___x_3594_);
v___x_3598_ = lean_array_push(v___x_3597_, v___x_3594_);
v___x_3599_ = lean_array_push(v___x_3598_, v___x_3595_);
v___x_3600_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3593_);
lean_ctor_set(v___x_3600_, 1, v___x_3583_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
v___x_3601_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3582_, v___x_3590_, v___x_3592_, v___x_3600_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; size_t v_sz_3603_; size_t v___x_3604_; lean_object* v___x_3605_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
v_sz_3603_ = lean_array_size(v_alts_3576_);
v___x_3604_ = ((size_t)0ULL);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3594_, v_sz_3603_, v___x_3604_, v_alts_3576_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3620_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v_fvarId_3610_; lean_object* v___x_3612_; 
v_fvarId_3610_ = lean_ctor_get(v_a_3602_, 0);
lean_inc(v_fvarId_3610_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 3, v_a_3606_);
lean_ctor_set(v___x_3578_, 2, v_fvarId_3610_);
lean_ctor_set(v___x_3578_, 1, v_a_3581_);
lean_ctor_set(v___x_3578_, 0, v___x_3591_);
v___x_3612_ = v___x_3578_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_a_3581_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_fvarId_3610_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_a_3606_);
v___x_3612_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3613_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_a_3602_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v_a_3588_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3615_);
v___x_3617_ = v___x_3608_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec(v_a_3602_);
lean_dec(v_a_3588_);
lean_dec(v_a_3581_);
lean_del_object(v___x_3578_);
v_a_3621_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3605_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3605_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec_ref_known(v___x_3594_, 1);
lean_dec(v_a_3588_);
lean_dec(v_a_3581_);
lean_del_object(v___x_3578_);
lean_dec_ref(v_alts_3576_);
v_a_3629_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3601_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3601_);
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
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_a_3581_);
lean_del_object(v___x_3578_);
lean_dec_ref(v_alts_3576_);
lean_dec(v_discr_3575_);
v_a_3637_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3587_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3587_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_del_object(v___x_3578_);
lean_dec_ref(v_alts_3576_);
lean_dec(v_discr_3575_);
v_a_3645_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3580_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3580_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3671_; lean_object* v___y_3672_; uint8_t v___y_3673_; lean_object* v___y_3678_; lean_object* v___y_3679_; uint8_t v___y_3680_; lean_object* v___y_3685_; lean_object* v___y_3686_; uint8_t v___y_3687_; lean_object* v_decl_3692_; lean_object* v_k_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; 
switch(lean_obj_tag(v_code_3655_))
{
case 0:
{
lean_object* v_decl_3738_; lean_object* v_k_3739_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v_value_3764_; 
v_decl_3738_ = lean_ctor_get(v_code_3655_, 0);
v_k_3739_ = lean_ctor_get(v_code_3655_, 1);
v_value_3764_ = lean_ctor_get(v_decl_3738_, 3);
lean_inc(v_value_3764_);
if (lean_obj_tag(v_value_3764_) == 3)
{
lean_object* v_declName_3765_; 
v_declName_3765_ = lean_ctor_get(v_value_3764_, 0);
lean_inc(v_declName_3765_);
if (lean_obj_tag(v_declName_3765_) == 1)
{
lean_object* v_pre_3766_; 
v_pre_3766_ = lean_ctor_get(v_declName_3765_, 0);
lean_inc(v_pre_3766_);
if (lean_obj_tag(v_pre_3766_) == 1)
{
lean_object* v_pre_3767_; 
v_pre_3767_ = lean_ctor_get(v_pre_3766_, 0);
if (lean_obj_tag(v_pre_3767_) == 0)
{
lean_object* v_type_3768_; lean_object* v_args_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3839_; 
v_type_3768_ = lean_ctor_get(v_decl_3738_, 2);
v_args_3769_ = lean_ctor_get(v_value_3764_, 2);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_value_3764_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; lean_object* v_unused_3841_; 
v_unused_3840_ = lean_ctor_get(v_value_3764_, 1);
lean_dec(v_unused_3840_);
v_unused_3841_ = lean_ctor_get(v_value_3764_, 0);
lean_dec(v_unused_3841_);
v___x_3771_ = v_value_3764_;
v_isShared_3772_ = v_isSharedCheck_3839_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_args_3769_);
lean_dec(v_value_3764_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3839_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_str_3773_; lean_object* v_str_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_str_3773_ = lean_ctor_get(v_declName_3765_, 1);
lean_inc_ref(v_str_3773_);
lean_dec_ref_known(v_declName_3765_, 2);
v_str_3774_ = lean_ctor_get(v_pre_3766_, 1);
lean_inc_ref(v_str_3774_);
lean_dec_ref_known(v_pre_3766_, 2);
v___x_3775_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_3776_ = lean_string_dec_eq(v_str_3774_, v___x_3775_);
lean_dec_ref(v_str_3774_);
if (v___x_3776_ == 0)
{
lean_dec_ref(v_str_3773_);
lean_del_object(v___x_3771_);
lean_dec_ref(v_args_3769_);
v___y_3741_ = v_a_3656_;
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3777_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_3778_ = lean_string_dec_eq(v_str_3773_, v___x_3777_);
lean_dec_ref(v_str_3773_);
if (v___x_3778_ == 0)
{
lean_del_object(v___x_3771_);
lean_dec_ref(v_args_3769_);
v___y_3741_ = v_a_3656_;
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3836_; 
lean_inc_ref(v_type_3768_);
lean_inc_ref(v_k_3739_);
lean_inc_ref(v_decl_3738_);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_code_3655_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; lean_object* v_unused_3838_; 
v_unused_3837_ = lean_ctor_get(v_code_3655_, 1);
lean_dec(v_unused_3837_);
v_unused_3838_ = lean_ctor_get(v_code_3655_, 0);
lean_dec(v_unused_3838_);
v___x_3780_ = v_code_3655_;
v_isShared_3781_ = v_isSharedCheck_3836_;
goto v_resetjp_3779_;
}
else
{
lean_dec(v_code_3655_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3836_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3782_ = lean_array_get_size(v_args_3769_);
v___x_3783_ = lean_unsigned_to_nat(1u);
v___x_3784_ = lean_nat_dec_eq(v___x_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_del_object(v___x_3780_);
lean_del_object(v___x_3771_);
lean_dec_ref(v_args_3769_);
lean_dec_ref(v_type_3768_);
lean_dec_ref(v_k_3739_);
lean_dec_ref(v_decl_3738_);
v___x_3785_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3786_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3785_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_3786_;
}
else
{
uint8_t v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3787_ = 0;
v___x_3788_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3));
v___x_3789_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_3790_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3787_, v___x_3788_, v___x_3789_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v_fvarId_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3803_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v_fvarId_3792_ = lean_ctor_get(v_a_3791_, 0);
v___x_3793_ = lean_unsigned_to_nat(0u);
v___x_3794_ = lean_array_fget(v_args_3769_, v___x_3793_);
lean_dec_ref(v_args_3769_);
v___x_3795_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3796_ = lean_box(0);
lean_inc(v_fvarId_3792_);
v___x_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_fvarId_3792_);
v___x_3798_ = lean_unsigned_to_nat(2u);
v___x_3799_ = lean_mk_empty_array_with_capacity(v___x_3798_);
v___x_3800_ = lean_array_push(v___x_3799_, v___x_3794_);
v___x_3801_ = lean_array_push(v___x_3800_, v___x_3797_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 2, v___x_3801_);
lean_ctor_set(v___x_3771_, 1, v___x_3796_);
lean_ctor_set(v___x_3771_, 0, v___x_3795_);
v___x_3803_ = v___x_3771_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v___x_3801_);
v___x_3803_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
lean_object* v___x_3804_; 
v___x_3804_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3787_, v_decl_3738_, v_type_3768_, v___x_3803_, v_a_3658_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___x_3806_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3739_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3818_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3818_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3818_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 1, v_a_3807_);
lean_ctor_set(v___x_3780_, 0, v_a_3805_);
v___x_3812_ = v___x_3780_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3805_);
lean_ctor_set(v_reuseFailAlloc_3817_, 1, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v_a_3791_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3813_);
v___x_3815_ = v___x_3809_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_dec(v_a_3805_);
lean_dec(v_a_3791_);
lean_del_object(v___x_3780_);
return v___x_3806_;
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
lean_dec(v_a_3791_);
lean_del_object(v___x_3780_);
lean_dec_ref(v_k_3739_);
v_a_3819_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3821_ = v___x_3804_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3804_);
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
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3780_);
lean_del_object(v___x_3771_);
lean_dec_ref(v_args_3769_);
lean_dec_ref(v_type_3768_);
lean_dec_ref(v_k_3739_);
lean_dec_ref(v_decl_3738_);
v_a_3828_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3790_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3790_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
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
lean_dec_ref_known(v_pre_3766_, 2);
lean_dec_ref_known(v_declName_3765_, 2);
lean_dec_ref_known(v_value_3764_, 3);
v___y_3741_ = v_a_3656_;
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
goto v___jp_3740_;
}
}
else
{
lean_dec(v_pre_3766_);
lean_dec_ref_known(v_declName_3765_, 2);
lean_dec_ref_known(v_value_3764_, 3);
v___y_3741_ = v_a_3656_;
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
goto v___jp_3740_;
}
}
else
{
lean_dec_ref_known(v_value_3764_, 3);
lean_dec(v_declName_3765_);
v___y_3741_ = v_a_3656_;
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
goto v___jp_3740_;
}
}
else
{
lean_dec(v_value_3764_);
v___y_3741_ = v_a_3656_;
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
goto v___jp_3740_;
}
v___jp_3740_:
{
lean_object* v___x_3746_; 
lean_inc_ref(v_decl_3738_);
v___x_3746_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3738_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
lean_inc_ref(v_k_3739_);
v___x_3748_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3739_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; size_t v___x_3750_; size_t v___x_3751_; uint8_t v___x_3752_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___x_3750_ = lean_ptr_addr(v_k_3739_);
v___x_3751_ = lean_ptr_addr(v_a_3749_);
v___x_3752_ = lean_usize_dec_eq(v___x_3750_, v___x_3751_);
if (v___x_3752_ == 0)
{
v___y_3671_ = v_a_3749_;
v___y_3672_ = v_a_3747_;
v___y_3673_ = v___x_3752_;
goto v___jp_3670_;
}
else
{
size_t v___x_3753_; size_t v___x_3754_; uint8_t v___x_3755_; 
v___x_3753_ = lean_ptr_addr(v_decl_3738_);
v___x_3754_ = lean_ptr_addr(v_a_3747_);
v___x_3755_ = lean_usize_dec_eq(v___x_3753_, v___x_3754_);
v___y_3671_ = v_a_3749_;
v___y_3672_ = v_a_3747_;
v___y_3673_ = v___x_3755_;
goto v___jp_3670_;
}
}
else
{
lean_dec(v_a_3747_);
lean_dec_ref_known(v_code_3655_, 2);
return v___x_3748_;
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec_ref_known(v_code_3655_, 2);
v_a_3756_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3746_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3746_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_3842_; lean_object* v_args_3843_; size_t v_sz_3844_; size_t v___x_3845_; lean_object* v___x_3846_; 
v_fvarId_3842_ = lean_ctor_get(v_code_3655_, 0);
v_args_3843_ = lean_ctor_get(v_code_3655_, 1);
v_sz_3844_ = lean_array_size(v_args_3843_);
v___x_3845_ = ((size_t)0ULL);
lean_inc_ref(v_args_3843_);
v___x_3846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3844_, v___x_3845_, v_args_3843_, v_a_3656_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3872_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3872_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3872_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
uint8_t v___y_3852_; uint8_t v___x_3868_; 
v___x_3868_ = l_Lean_instBEqFVarId_beq(v_fvarId_3842_, v_fvarId_3842_);
if (v___x_3868_ == 0)
{
v___y_3852_ = v___x_3868_;
goto v___jp_3851_;
}
else
{
size_t v___x_3869_; size_t v___x_3870_; uint8_t v___x_3871_; 
v___x_3869_ = lean_ptr_addr(v_args_3843_);
v___x_3870_ = lean_ptr_addr(v_a_3847_);
v___x_3871_ = lean_usize_dec_eq(v___x_3869_, v___x_3870_);
v___y_3852_ = v___x_3871_;
goto v___jp_3851_;
}
v___jp_3851_:
{
if (v___y_3852_ == 0)
{
lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3862_; 
lean_inc(v_fvarId_3842_);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_code_3655_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; lean_object* v_unused_3864_; 
v_unused_3863_ = lean_ctor_get(v_code_3655_, 1);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_code_3655_, 0);
lean_dec(v_unused_3864_);
v___x_3854_ = v_code_3655_;
v_isShared_3855_ = v_isSharedCheck_3862_;
goto v_resetjp_3853_;
}
else
{
lean_dec(v_code_3655_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3862_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 1, v_a_3847_);
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_fvarId_3842_);
lean_ctor_set(v_reuseFailAlloc_3861_, 1, v_a_3847_);
v___x_3857_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3859_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3857_);
v___x_3859_ = v___x_3849_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
else
{
lean_object* v___x_3866_; 
lean_dec(v_a_3847_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v_code_3655_);
v___x_3866_ = v___x_3849_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_code_3655_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref_known(v_code_3655_, 2);
v_a_3873_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3846_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3846_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
case 4:
{
lean_object* v_cases_3881_; lean_object* v_typeName_3882_; lean_object* v_resultType_3883_; lean_object* v_discr_3884_; lean_object* v_alts_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v_cases_3881_ = lean_ctor_get(v_code_3655_, 0);
lean_inc_ref(v_cases_3881_);
v_typeName_3882_ = lean_ctor_get(v_cases_3881_, 0);
v_resultType_3883_ = lean_ctor_get(v_cases_3881_, 1);
v_discr_3884_ = lean_ctor_get(v_cases_3881_, 2);
v_alts_3885_ = lean_ctor_get(v_cases_3881_, 3);
v___x_3886_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__8));
v___x_3887_ = lean_name_eq(v_typeName_3882_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3889_ = lean_name_eq(v_typeName_3882_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3891_ = lean_name_eq(v_typeName_3882_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3892_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__10));
v___x_3893_ = lean_name_eq(v_typeName_3882_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__12));
v___x_3895_ = lean_name_eq(v_typeName_3882_, v___x_3894_);
if (v___x_3895_ == 0)
{
lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3896_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__14));
v___x_3897_ = lean_name_eq(v_typeName_3882_, v___x_3896_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3898_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3899_ = lean_name_eq(v_typeName_3882_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3901_ = lean_name_eq(v_typeName_3882_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; uint8_t v___x_3903_; 
v___x_3902_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3903_ = lean_name_eq(v_typeName_3882_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; uint8_t v___x_3905_; 
v___x_3904_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3905_ = lean_name_eq(v_typeName_3882_, v___x_3904_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3906_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3907_ = lean_name_eq(v_typeName_3882_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; uint8_t v___x_3909_; 
v___x_3908_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3909_ = lean_name_eq(v_typeName_3882_, v___x_3908_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; uint8_t v___x_3911_; 
v___x_3910_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3911_ = lean_name_eq(v_typeName_3882_, v___x_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; uint8_t v___x_3913_; 
v___x_3912_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3913_ = lean_name_eq(v_typeName_3882_, v___x_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; uint8_t v___x_3915_; 
v___x_3914_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__24));
v___x_3915_ = lean_name_eq(v_typeName_3882_, v___x_3914_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
lean_inc(v_typeName_3882_);
v___x_3916_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3882_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
if (lean_obj_tag(v_a_3917_) == 1)
{
lean_object* v_val_3918_; lean_object* v___x_3919_; 
lean_dec_ref_known(v_code_3655_, 1);
v_val_3918_ = lean_ctor_get(v_a_3917_, 0);
lean_inc(v_val_3918_);
lean_dec_ref_known(v_a_3917_, 1);
v___x_3919_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3918_, v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec(v_val_3918_);
return v___x_3919_;
}
else
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_4012_; 
lean_inc_ref(v_alts_3885_);
lean_inc(v_discr_3884_);
lean_inc_ref(v_resultType_3883_);
lean_inc(v_typeName_3882_);
lean_dec(v_a_3917_);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_cases_3881_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; 
v_unused_4013_ = lean_ctor_get(v_cases_3881_, 3);
lean_dec(v_unused_4013_);
v_unused_4014_ = lean_ctor_get(v_cases_3881_, 2);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_cases_3881_, 1);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_cases_3881_, 0);
lean_dec(v_unused_4016_);
v___x_3921_ = v_cases_3881_;
v_isShared_3922_ = v_isSharedCheck_4012_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v_cases_3881_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_4012_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; 
lean_inc_ref(v_resultType_3883_);
v___x_3923_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3883_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_4003_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3926_ = v___x_3923_;
v_isShared_3927_ = v_isSharedCheck_4003_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3923_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_4003_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v_env_3929_; lean_object* v___x_3956_; 
v___x_3928_ = lean_st_ref_get(v_a_3660_);
v_env_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc_ref_n(v_env_3929_, 2);
lean_dec(v___x_3928_);
lean_inc(v_typeName_3882_);
v___x_3956_ = l_Lean_Environment_find_x3f(v_env_3929_, v_typeName_3882_, v___x_3915_);
if (lean_obj_tag(v___x_3956_) == 1)
{
lean_object* v_val_3957_; 
v_val_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_val_3957_);
lean_dec_ref_known(v___x_3956_, 1);
if (lean_obj_tag(v_val_3957_) == 5)
{
lean_object* v_val_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4002_; 
v_val_3958_ = lean_ctor_get(v_val_3957_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_val_3957_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3960_ = v_val_3957_;
v_isShared_3961_ = v_isSharedCheck_4002_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_val_3958_);
lean_dec(v_val_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4002_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_toConstantVal_3962_; lean_object* v_name_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v_toConstantVal_3962_ = lean_ctor_get(v_val_3958_, 0);
lean_inc_ref(v_toConstantVal_3962_);
lean_dec_ref(v_val_3958_);
v_name_3963_ = lean_ctor_get(v_toConstantVal_3962_, 0);
lean_inc(v_name_3963_);
lean_dec_ref(v_toConstantVal_3962_);
v___x_3964_ = l_Lean_mkCasesOnName(v_name_3963_);
lean_inc_ref(v_env_3929_);
v___x_3965_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3929_, v___x_3964_);
if (lean_obj_tag(v___x_3965_) == 0)
{
if (v___x_3915_ == 0)
{
size_t v_sz_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
lean_dec_ref(v_env_3929_);
lean_del_object(v___x_3921_);
v_sz_3966_ = lean_array_size(v_alts_3885_);
v___x_3967_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3885_);
v___x_3968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_3966_, v___x_3967_, v_alts_3885_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3993_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3971_ = v___x_3968_;
v_isShared_3972_ = v_isSharedCheck_3993_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3968_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3993_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
uint8_t v___y_3982_; size_t v___x_3987_; size_t v___x_3988_; uint8_t v___x_3989_; 
v___x_3987_ = lean_ptr_addr(v_alts_3885_);
lean_dec_ref(v_alts_3885_);
v___x_3988_ = lean_ptr_addr(v_a_3969_);
v___x_3989_ = lean_usize_dec_eq(v___x_3987_, v___x_3988_);
if (v___x_3989_ == 0)
{
lean_dec_ref(v_resultType_3883_);
v___y_3982_ = v___x_3989_;
goto v___jp_3981_;
}
else
{
size_t v___x_3990_; size_t v___x_3991_; uint8_t v___x_3992_; 
v___x_3990_ = lean_ptr_addr(v_resultType_3883_);
lean_dec_ref(v_resultType_3883_);
v___x_3991_ = lean_ptr_addr(v_a_3924_);
v___x_3992_ = lean_usize_dec_eq(v___x_3990_, v___x_3991_);
v___y_3982_ = v___x_3992_;
goto v___jp_3981_;
}
v___jp_3973_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3974_, 0, v_typeName_3882_);
lean_ctor_set(v___x_3974_, 1, v_a_3924_);
lean_ctor_set(v___x_3974_, 2, v_discr_3884_);
lean_ctor_set(v___x_3974_, 3, v_a_3969_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set_tag(v___x_3960_, 4);
lean_ctor_set(v___x_3960_, 0, v___x_3974_);
v___x_3976_ = v___x_3960_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3978_; 
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3976_);
v___x_3978_ = v___x_3971_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
v___jp_3981_:
{
if (v___y_3982_ == 0)
{
lean_del_object(v___x_3926_);
lean_dec_ref_known(v_code_3655_, 1);
goto v___jp_3973_;
}
else
{
uint8_t v___x_3983_; 
v___x_3983_ = l_Lean_instBEqFVarId_beq(v_discr_3884_, v_discr_3884_);
if (v___x_3983_ == 0)
{
lean_del_object(v___x_3926_);
lean_dec_ref_known(v_code_3655_, 1);
goto v___jp_3973_;
}
else
{
lean_object* v___x_3985_; 
lean_del_object(v___x_3971_);
lean_dec(v_a_3969_);
lean_del_object(v___x_3960_);
lean_dec(v_a_3924_);
lean_dec(v_discr_3884_);
lean_dec(v_typeName_3882_);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 0, v_code_3655_);
v___x_3985_ = v___x_3926_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_code_3655_);
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
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_del_object(v___x_3960_);
lean_del_object(v___x_3926_);
lean_dec(v_a_3924_);
lean_dec_ref(v_alts_3885_);
lean_dec(v_discr_3884_);
lean_dec_ref(v_resultType_3883_);
lean_dec(v_typeName_3882_);
lean_dec_ref_known(v_code_3655_, 1);
v_a_3994_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3968_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3968_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
lean_del_object(v___x_3960_);
lean_del_object(v___x_3926_);
lean_dec_ref(v_resultType_3883_);
lean_dec_ref_known(v_code_3655_, 1);
goto v___jp_3930_;
}
}
else
{
lean_dec_ref_known(v___x_3965_, 1);
lean_del_object(v___x_3960_);
lean_del_object(v___x_3926_);
lean_dec_ref(v_resultType_3883_);
lean_dec_ref_known(v_code_3655_, 1);
goto v___jp_3930_;
}
}
}
else
{
lean_dec(v_val_3957_);
lean_dec_ref(v_env_3929_);
lean_del_object(v___x_3926_);
lean_dec(v_a_3924_);
lean_del_object(v___x_3921_);
lean_dec_ref(v_alts_3885_);
lean_dec(v_discr_3884_);
lean_dec_ref(v_resultType_3883_);
lean_dec(v_typeName_3882_);
lean_dec_ref_known(v_code_3655_, 1);
v___y_3663_ = v_a_3656_;
v___y_3664_ = v_a_3657_;
v___y_3665_ = v_a_3658_;
v___y_3666_ = v_a_3659_;
v___y_3667_ = v_a_3660_;
goto v___jp_3662_;
}
}
else
{
lean_dec(v___x_3956_);
lean_dec_ref(v_env_3929_);
lean_del_object(v___x_3926_);
lean_dec(v_a_3924_);
lean_del_object(v___x_3921_);
lean_dec_ref(v_alts_3885_);
lean_dec(v_discr_3884_);
lean_dec_ref(v_resultType_3883_);
lean_dec(v_typeName_3882_);
lean_dec_ref_known(v_code_3655_, 1);
v___y_3663_ = v_a_3656_;
v___y_3664_ = v_a_3657_;
v___y_3665_ = v_a_3658_;
v___y_3666_ = v_a_3659_;
v___y_3667_ = v_a_3660_;
goto v___jp_3662_;
}
v___jp_3930_:
{
size_t v_sz_3931_; size_t v___x_3932_; lean_object* v___x_3933_; 
v_sz_3931_ = lean_array_size(v_alts_3885_);
v___x_3932_ = ((size_t)0ULL);
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_env_3929_, v___x_3915_, v_sz_3931_, v___x_3932_, v_alts_3885_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3947_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3936_ = v___x_3933_;
v_isShared_3937_ = v_isSharedCheck_3947_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3947_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3938_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_3939_ = l_Lean_Name_append(v_typeName_3882_, v___x_3938_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 3, v_a_3934_);
lean_ctor_set(v___x_3921_, 1, v_a_3924_);
lean_ctor_set(v___x_3921_, 0, v___x_3939_);
v___x_3941_ = v___x_3921_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_a_3924_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_discr_3884_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_a_3934_);
v___x_3941_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3941_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v___x_3942_);
v___x_3944_ = v___x_3936_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec(v_a_3924_);
lean_del_object(v___x_3921_);
lean_dec(v_discr_3884_);
lean_dec(v_typeName_3882_);
v_a_3948_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3933_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3933_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v_a_3948_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
}
}
}
}
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_del_object(v___x_3921_);
lean_dec_ref(v_alts_3885_);
lean_dec(v_discr_3884_);
lean_dec_ref(v_resultType_3883_);
lean_dec(v_typeName_3882_);
lean_dec_ref_known(v_code_3655_, 1);
v_a_4004_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3923_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3923_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref_known(v_code_3655_, 1);
lean_dec_ref(v_cases_3881_);
v_a_4017_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3916_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3916_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_object* v___x_4025_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4025_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4025_;
}
}
else
{
lean_object* v___x_4026_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4026_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
lean_dec_ref(v_cases_3881_);
return v___x_4026_;
}
}
else
{
lean_object* v___x_4027_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4027_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4027_;
}
}
else
{
lean_object* v___x_4028_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4028_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4028_;
}
}
else
{
lean_object* v___x_4029_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4029_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4029_;
}
}
else
{
lean_object* v___x_4030_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4030_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4030_;
}
}
else
{
lean_object* v___x_4031_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4031_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4031_;
}
}
else
{
lean_object* v___x_4032_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4032_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4032_;
}
}
else
{
lean_object* v___x_4033_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4033_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3881_, v___x_3898_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4033_;
}
}
else
{
lean_object* v___x_4034_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4034_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3881_, v___x_3896_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4034_;
}
}
else
{
lean_object* v___x_4035_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4035_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3881_, v___x_3894_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4035_;
}
}
else
{
lean_object* v___x_4036_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4036_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3881_, v___x_3892_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4036_;
}
}
else
{
lean_object* v___x_4037_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4037_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4037_;
}
}
else
{
lean_object* v___x_4038_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4038_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4038_;
}
}
else
{
lean_object* v___x_4039_; 
lean_dec_ref_known(v_code_3655_, 1);
v___x_4039_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_cases_3881_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
return v___x_4039_;
}
}
case 5:
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4040_, 0, v_code_3655_);
return v___x_4040_;
}
case 6:
{
lean_object* v_type_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4065_; 
v_type_4041_ = lean_ctor_get(v_code_3655_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_code_3655_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4043_ = v_code_3655_;
v_isShared_4044_ = v_isSharedCheck_4065_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_type_4041_);
lean_dec(v_code_3655_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4065_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4041_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4056_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4045_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4056_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 0, v_a_4046_);
v___x_4051_ = v___x_4043_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4053_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v___x_4051_);
v___x_4053_ = v___x_4048_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v___x_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_del_object(v___x_4043_);
v_a_4057_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4045_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4045_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
default: 
{
lean_object* v_decl_4066_; lean_object* v_k_4067_; 
v_decl_4066_ = lean_ctor_get(v_code_3655_, 0);
v_k_4067_ = lean_ctor_get(v_code_3655_, 1);
lean_inc_ref(v_k_4067_);
lean_inc_ref(v_decl_4066_);
v_decl_3692_ = v_decl_4066_;
v_k_3693_ = v_k_4067_;
v___y_3694_ = v_a_3656_;
v___y_3695_ = v_a_3657_;
v___y_3696_ = v_a_3658_;
v___y_3697_ = v_a_3659_;
v___y_3698_ = v_a_3660_;
goto v___jp_3691_;
}
}
v___jp_3662_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__1, &l_Lean_Compiler_LCNF_Code_toMono___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1);
v___x_3669_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3668_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
return v___x_3669_;
}
v___jp_3670_:
{
if (v___y_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec_ref(v_code_3655_);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___y_3672_);
lean_ctor_set(v___x_3674_, 1, v___y_3671_);
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
else
{
lean_object* v___x_3676_; 
lean_dec_ref(v___y_3672_);
lean_dec_ref(v___y_3671_);
v___x_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3676_, 0, v_code_3655_);
return v___x_3676_;
}
}
v___jp_3677_:
{
if (v___y_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref(v_code_3655_);
v___x_3681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___y_3679_);
lean_ctor_set(v___x_3681_, 1, v___y_3678_);
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; 
lean_dec_ref(v___y_3679_);
lean_dec_ref(v___y_3678_);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v_code_3655_);
return v___x_3683_;
}
}
v___jp_3684_:
{
if (v___y_3687_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_dec_ref(v_code_3655_);
v___x_3688_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___y_3686_);
lean_ctor_set(v___x_3688_, 1, v___y_3685_);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
else
{
lean_object* v___x_3690_; 
lean_dec_ref(v___y_3686_);
lean_dec_ref(v___y_3685_);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v_code_3655_);
return v___x_3690_;
}
}
v___jp_3691_:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3692_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3701_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref_known(v___x_3699_, 1);
v___x_3701_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
if (lean_obj_tag(v___x_3701_) == 0)
{
switch(lean_obj_tag(v_code_3655_))
{
case 1:
{
lean_object* v_a_3702_; lean_object* v_decl_3703_; lean_object* v_k_3704_; size_t v___x_3705_; size_t v___x_3706_; uint8_t v___x_3707_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3702_);
lean_dec_ref_known(v___x_3701_, 1);
v_decl_3703_ = lean_ctor_get(v_code_3655_, 0);
v_k_3704_ = lean_ctor_get(v_code_3655_, 1);
v___x_3705_ = lean_ptr_addr(v_k_3704_);
v___x_3706_ = lean_ptr_addr(v_a_3702_);
v___x_3707_ = lean_usize_dec_eq(v___x_3705_, v___x_3706_);
if (v___x_3707_ == 0)
{
v___y_3678_ = v_a_3702_;
v___y_3679_ = v_a_3700_;
v___y_3680_ = v___x_3707_;
goto v___jp_3677_;
}
else
{
size_t v___x_3708_; size_t v___x_3709_; uint8_t v___x_3710_; 
v___x_3708_ = lean_ptr_addr(v_decl_3703_);
v___x_3709_ = lean_ptr_addr(v_a_3700_);
v___x_3710_ = lean_usize_dec_eq(v___x_3708_, v___x_3709_);
v___y_3678_ = v_a_3702_;
v___y_3679_ = v_a_3700_;
v___y_3680_ = v___x_3710_;
goto v___jp_3677_;
}
}
case 2:
{
lean_object* v_a_3711_; lean_object* v_decl_3712_; lean_object* v_k_3713_; size_t v___x_3714_; size_t v___x_3715_; uint8_t v___x_3716_; 
v_a_3711_ = lean_ctor_get(v___x_3701_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3701_, 1);
v_decl_3712_ = lean_ctor_get(v_code_3655_, 0);
v_k_3713_ = lean_ctor_get(v_code_3655_, 1);
v___x_3714_ = lean_ptr_addr(v_k_3713_);
v___x_3715_ = lean_ptr_addr(v_a_3711_);
v___x_3716_ = lean_usize_dec_eq(v___x_3714_, v___x_3715_);
if (v___x_3716_ == 0)
{
v___y_3685_ = v_a_3711_;
v___y_3686_ = v_a_3700_;
v___y_3687_ = v___x_3716_;
goto v___jp_3684_;
}
else
{
size_t v___x_3717_; size_t v___x_3718_; uint8_t v___x_3719_; 
v___x_3717_ = lean_ptr_addr(v_decl_3712_);
v___x_3718_ = lean_ptr_addr(v_a_3700_);
v___x_3719_ = lean_usize_dec_eq(v___x_3717_, v___x_3718_);
v___y_3685_ = v_a_3711_;
v___y_3686_ = v_a_3700_;
v___y_3687_ = v___x_3719_;
goto v___jp_3684_;
}
}
default: 
{
lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3728_; 
lean_dec(v_a_3700_);
lean_dec_ref(v_code_3655_);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; 
v_unused_3729_ = lean_ctor_get(v___x_3701_, 0);
lean_dec(v_unused_3729_);
v___x_3721_ = v___x_3701_;
v_isShared_3722_ = v_isSharedCheck_3728_;
goto v_resetjp_3720_;
}
else
{
lean_dec(v___x_3701_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3728_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3723_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3724_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3723_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3724_);
v___x_3726_ = v___x_3721_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
else
{
lean_dec(v_a_3700_);
lean_dec_ref(v_code_3655_);
return v___x_3701_;
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v_k_3693_);
lean_dec_ref(v_code_3655_);
v_a_3730_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3699_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3699_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(size_t v_sz_4068_, size_t v_i_4069_, lean_object* v_bs_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v___x_4077_; 
v___x_4077_ = lean_usize_dec_lt(v_i_4069_, v_sz_4068_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_bs_4070_);
return v___x_4078_;
}
else
{
lean_object* v_v_4079_; lean_object* v___x_4080_; lean_object* v_bs_x27_4081_; lean_object* v_a_4083_; 
v_v_4079_ = lean_array_uget(v_bs_4070_, v_i_4069_);
v___x_4080_ = lean_unsigned_to_nat(0u);
v_bs_x27_4081_ = lean_array_uset(v_bs_4070_, v_i_4069_, v___x_4080_);
if (lean_obj_tag(v_v_4079_) == 0)
{
lean_object* v_ctorName_4088_; lean_object* v_params_4089_; lean_object* v_code_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4124_; 
v_ctorName_4088_ = lean_ctor_get(v_v_4079_, 0);
v_params_4089_ = lean_ctor_get(v_v_4079_, 1);
v_code_4090_ = lean_ctor_get(v_v_4079_, 2);
v_isSharedCheck_4124_ = !lean_is_exclusive(v_v_4079_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4092_ = v_v_4079_;
v_isShared_4093_ = v_isSharedCheck_4124_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_code_4090_);
lean_inc(v_params_4089_);
lean_inc(v_ctorName_4088_);
lean_dec(v_v_4079_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4124_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
uint8_t v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = 0;
v___x_4095_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_4094_, v_params_4089_, v___y_4073_);
lean_dec_ref(v_params_4089_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v___y_4097_; lean_object* v___x_4112_; uint8_t v___x_4113_; 
lean_dec_ref_known(v___x_4095_, 1);
v___x_4112_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_4113_ = lean_name_eq(v_ctorName_4088_, v___x_4112_);
lean_dec(v_ctorName_4088_);
if (v___x_4113_ == 0)
{
lean_object* v___x_4114_; 
v___x_4114_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___y_4097_ = v___x_4114_;
goto v___jp_4096_;
}
else
{
lean_object* v___x_4115_; 
v___x_4115_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___y_4097_ = v___x_4115_;
goto v___jp_4096_;
}
v___jp_4096_:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4090_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; lean_object* v___x_4102_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
lean_inc(v___y_4097_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 2, v_a_4099_);
lean_ctor_set(v___x_4092_, 1, v___x_4100_);
lean_ctor_set(v___x_4092_, 0, v___y_4097_);
v___x_4102_ = v___x_4092_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___y_4097_);
lean_ctor_set(v_reuseFailAlloc_4103_, 1, v___x_4100_);
lean_ctor_set(v_reuseFailAlloc_4103_, 2, v_a_4099_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
v_a_4083_ = v___x_4102_;
goto v___jp_4082_;
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_del_object(v___x_4092_);
lean_dec_ref(v_bs_x27_4081_);
v_a_4104_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4098_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4098_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_del_object(v___x_4092_);
lean_dec_ref(v_code_4090_);
lean_dec(v_ctorName_4088_);
lean_dec_ref(v_bs_x27_4081_);
v_a_4116_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4095_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4095_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
else
{
lean_object* v_code_4125_; lean_object* v___x_4126_; 
v_code_4125_ = lean_ctor_get(v_v_4079_, 0);
lean_inc_ref(v_code_4125_);
v___x_4126_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4125_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4128_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_4079_, v_a_4127_);
v_a_4083_ = v___x_4128_;
goto v___jp_4082_;
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref_known(v_v_4079_, 1);
lean_dec_ref(v_bs_x27_4081_);
v_a_4129_ = lean_ctor_get(v___x_4126_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4126_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4126_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4126_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
v___jp_4082_:
{
size_t v___x_4084_; size_t v___x_4085_; lean_object* v___x_4086_; 
v___x_4084_ = ((size_t)1ULL);
v___x_4085_ = lean_usize_add(v_i_4069_, v___x_4084_);
v___x_4086_ = lean_array_uset(v_bs_x27_4081_, v_i_4069_, v_a_4083_);
v_i_4069_ = v___x_4085_;
v_bs_4070_ = v___x_4086_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object* v_c_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_){
_start:
{
lean_object* v_resultType_4144_; lean_object* v_discr_4145_; lean_object* v_alts_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4184_; 
v_resultType_4144_ = lean_ctor_get(v_c_4137_, 1);
v_discr_4145_ = lean_ctor_get(v_c_4137_, 2);
v_alts_4146_ = lean_ctor_get(v_c_4137_, 3);
v_isSharedCheck_4184_ = !lean_is_exclusive(v_c_4137_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; 
v_unused_4185_ = lean_ctor_get(v_c_4137_, 0);
lean_dec(v_unused_4185_);
v___x_4148_ = v_c_4137_;
v_isShared_4149_ = v_isSharedCheck_4184_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_alts_4146_);
lean_inc(v_discr_4145_);
lean_inc(v_resultType_4144_);
lean_dec(v_c_4137_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4184_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_4144_, v_a_4141_, v_a_4142_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; size_t v_sz_4152_; size_t v___x_4153_; lean_object* v___x_4154_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v_sz_4152_ = lean_array_size(v_alts_4146_);
v___x_4153_ = ((size_t)0ULL);
v___x_4154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(v_sz_4152_, v___x_4153_, v_alts_4146_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4167_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4157_ = v___x_4154_;
v_isShared_4158_ = v_isSharedCheck_4167_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4167_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4159_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 3, v_a_4155_);
lean_ctor_set(v___x_4148_, 1, v_a_4151_);
lean_ctor_set(v___x_4148_, 0, v___x_4159_);
v___x_4161_ = v___x_4148_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v_a_4151_);
lean_ctor_set(v_reuseFailAlloc_4166_, 2, v_discr_4145_);
lean_ctor_set(v_reuseFailAlloc_4166_, 3, v_a_4155_);
v___x_4161_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4162_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v___x_4162_);
v___x_4164_ = v___x_4157_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_a_4151_);
lean_del_object(v___x_4148_);
lean_dec(v_discr_4145_);
v_a_4168_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4154_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4154_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_del_object(v___x_4148_);
lean_dec_ref(v_alts_4146_);
lean_dec(v_discr_4145_);
v_a_4176_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4150_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4150_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object* v_c_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_);
lean_dec(v_a_4199_);
lean_dec_ref(v_a_4198_);
lean_dec(v_a_4197_);
lean_dec_ref(v_a_4196_);
lean_dec(v_a_4195_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_4202_, lean_object* v_i_4203_, lean_object* v_bs_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
size_t v_sz_boxed_4211_; size_t v_i_boxed_4212_; lean_object* v_res_4213_; 
v_sz_boxed_4211_ = lean_unbox_usize(v_sz_4202_);
lean_dec(v_sz_4202_);
v_i_boxed_4212_ = lean_unbox_usize(v_i_4203_);
lean_dec(v_i_4203_);
v_res_4213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_4211_, v_i_boxed_4212_, v_bs_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___boxed(lean_object* v_sz_4214_, lean_object* v_i_4215_, lean_object* v_bs_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
size_t v_sz_boxed_4223_; size_t v_i_boxed_4224_; lean_object* v_res_4225_; 
v_sz_boxed_4223_ = lean_unbox_usize(v_sz_4214_);
lean_dec(v_sz_4214_);
v_i_boxed_4224_ = lean_unbox_usize(v_i_4215_);
lean_dec(v_i_4215_);
v_res_4225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(v_sz_boxed_4223_, v_i_boxed_4224_, v_bs_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
lean_dec(v_a_4227_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_4234_, lean_object* v_uintName_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4234_, v_uintName_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
lean_dec(v_a_4248_);
lean_dec_ref(v_a_4247_);
lean_dec(v_a_4246_);
lean_dec_ref(v_a_4245_);
lean_dec(v_a_4244_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
lean_dec(v_a_4268_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v_sz_4285_, lean_object* v_i_4286_, lean_object* v_bs_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
uint8_t v___x_47244__boxed_4294_; size_t v_sz_boxed_4295_; size_t v_i_boxed_4296_; lean_object* v_res_4297_; 
v___x_47244__boxed_4294_ = lean_unbox(v___x_4284_);
v_sz_boxed_4295_ = lean_unbox_usize(v_sz_4285_);
lean_dec(v_sz_4285_);
v_i_boxed_4296_ = lean_unbox_usize(v_i_4286_);
lean_dec(v_i_4286_);
v_res_4297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_4283_, v___x_47244__boxed_4294_, v_sz_boxed_4295_, v_i_boxed_4296_, v_bs_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
lean_dec(v_a_4303_);
lean_dec_ref(v_a_4302_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_a_4309_);
lean_dec_ref(v_a_4308_);
lean_dec(v_a_4307_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_4322_, lean_object* v_c_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_4322_, v_c_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec_ref(v_a_4325_);
lean_dec(v_a_4324_);
lean_dec_ref(v_info_4322_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_4331_, lean_object* v_sz_4332_, lean_object* v_i_4333_, lean_object* v_bs_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
size_t v_sz_boxed_4341_; size_t v_i_boxed_4342_; lean_object* v_res_4343_; 
v_sz_boxed_4341_ = lean_unbox_usize(v_sz_4332_);
lean_dec(v_sz_4332_);
v_i_boxed_4342_ = lean_unbox_usize(v_i_4333_);
lean_dec(v_i_4333_);
v_res_4343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_4331_, v_sz_boxed_4341_, v_i_boxed_4342_, v_bs_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
return v_res_4343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_c_4344_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_4352_, lean_object* v_sz_4353_, lean_object* v_i_4354_, lean_object* v_bs_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
size_t v_sz_boxed_4362_; size_t v_i_boxed_4363_; lean_object* v_res_4364_; 
v_sz_boxed_4362_ = lean_unbox_usize(v_sz_4353_);
lean_dec(v_sz_4353_);
v_i_boxed_4363_ = lean_unbox_usize(v_i_4354_);
lean_dec(v_i_4354_);
v_res_4364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_4352_, v_sz_boxed_4362_, v_i_boxed_4363_, v_bs_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4373_, lean_object* v_x_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_){
_start:
{
lean_object* v___x_4381_; 
v___x_4381_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4373_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4382_, lean_object* v_x_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_){
_start:
{
lean_object* v_res_4390_; 
v_res_4390_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4382_, v_x_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
lean_dec(v_a_4386_);
lean_dec_ref(v_a_4385_);
lean_dec(v_a_4384_);
return v_res_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4391_, lean_object* v_x_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4391_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4400_, lean_object* v_x_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4400_, v_x_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_c_4400_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4409_, lean_object* v_x_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4409_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_);
return v___x_4417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4418_, lean_object* v_x_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4418_, v_x_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
lean_dec(v_a_4420_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4427_, lean_object* v_x_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4427_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4436_, lean_object* v_x_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4436_, v_x_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
lean_dec(v_a_4442_);
lean_dec_ref(v_a_4441_);
lean_dec(v_a_4440_);
lean_dec_ref(v_a_4439_);
lean_dec(v_a_4438_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4445_, lean_object* v_x_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4445_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4454_, lean_object* v_x_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4454_, v_x_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4463_, lean_object* v_x_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4463_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4472_, lean_object* v_x_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4472_, v_x_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_);
lean_dec(v_a_4478_);
lean_dec_ref(v_a_4477_);
lean_dec(v_a_4476_);
lean_dec_ref(v_a_4475_);
lean_dec(v_a_4474_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4481_, lean_object* v_x_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4481_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
return v___x_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4490_, lean_object* v_x_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4490_, v_x_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_a_4494_);
lean_dec_ref(v_a_4493_);
lean_dec(v_a_4492_);
return v_res_4498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4499_, lean_object* v_x_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v___x_4507_; 
v___x_4507_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4499_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4508_, lean_object* v_x_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4508_, v_x_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4517_, lean_object* v_uintName_4518_, lean_object* v_x_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
lean_object* v___x_4526_; 
v___x_4526_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4517_, v_uintName_4518_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_);
return v___x_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4527_, lean_object* v_uintName_4528_, lean_object* v_x_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4527_, v_uintName_4528_, v_x_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4537_, lean_object* v_x_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_){
_start:
{
lean_object* v___x_4545_; 
v___x_4545_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4537_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4546_, lean_object* v_x_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4546_, v_x_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4555_, lean_object* v_x_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4555_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4564_, lean_object* v_x_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4564_, v_x_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object* v_c_4573_, lean_object* v_x_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v___x_4581_; 
v___x_4581_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4573_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
return v___x_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___boxed(lean_object* v_c_4582_, lean_object* v_x_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
lean_object* v_res_4590_; 
v_res_4590_ = l_Lean_Compiler_LCNF_decToMono(v_c_4582_, v_x_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec(v_a_4584_);
return v_res_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4591_, size_t v_i_4592_, lean_object* v_bs_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v___x_4600_; 
v___x_4600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4591_, v_i_4592_, v_bs_4593_, v___y_4594_, v___y_4596_, v___y_4597_, v___y_4598_);
return v___x_4600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4601_, lean_object* v_i_4602_, lean_object* v_bs_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
size_t v_sz_boxed_4610_; size_t v_i_boxed_4611_; lean_object* v_res_4612_; 
v_sz_boxed_4610_ = lean_unbox_usize(v_sz_4601_);
lean_dec(v_sz_4601_);
v_i_boxed_4611_ = lean_unbox_usize(v_i_4602_);
lean_dec(v_i_4602_);
v_res_4612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4610_, v_i_boxed_4611_, v_bs_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4613_, lean_object* v_v_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
if (lean_obj_tag(v_v_4614_) == 0)
{
lean_object* v_code_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4645_; 
v_code_4621_ = lean_ctor_get(v_v_4614_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v_v_4614_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4623_ = v_v_4614_;
v_isShared_4624_ = v_isSharedCheck_4645_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_code_4621_);
lean_dec(v_v_4614_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4645_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4625_; 
lean_inc(v___y_4619_);
lean_inc_ref(v___y_4618_);
lean_inc(v___y_4617_);
lean_inc_ref(v___y_4616_);
lean_inc(v___y_4615_);
v___x_4625_ = lean_apply_7(v_f_4613_, v_code_4621_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, lean_box(0));
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; lean_object* v___x_4628_; uint8_t v_isShared_4629_; uint8_t v_isSharedCheck_4636_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4636_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4636_ == 0)
{
v___x_4628_ = v___x_4625_;
v_isShared_4629_ = v_isSharedCheck_4636_;
goto v_resetjp_4627_;
}
else
{
lean_inc(v_a_4626_);
lean_dec(v___x_4625_);
v___x_4628_ = lean_box(0);
v_isShared_4629_ = v_isSharedCheck_4636_;
goto v_resetjp_4627_;
}
v_resetjp_4627_:
{
lean_object* v___x_4631_; 
if (v_isShared_4624_ == 0)
{
lean_ctor_set(v___x_4623_, 0, v_a_4626_);
v___x_4631_ = v___x_4623_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v_a_4626_);
v___x_4631_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4633_; 
if (v_isShared_4629_ == 0)
{
lean_ctor_set(v___x_4628_, 0, v___x_4631_);
v___x_4633_ = v___x_4628_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_a_4637_; lean_object* v___x_4639_; uint8_t v_isShared_4640_; uint8_t v_isSharedCheck_4644_; 
lean_del_object(v___x_4623_);
v_a_4637_ = lean_ctor_get(v___x_4625_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4625_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4639_ = v___x_4625_;
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
else
{
lean_inc(v_a_4637_);
lean_dec(v___x_4625_);
v___x_4639_ = lean_box(0);
v_isShared_4640_ = v_isSharedCheck_4644_;
goto v_resetjp_4638_;
}
v_resetjp_4638_:
{
lean_object* v___x_4642_; 
if (v_isShared_4640_ == 0)
{
v___x_4642_ = v___x_4639_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4637_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
}
}
else
{
lean_object* v___x_4646_; 
lean_dec_ref(v_f_4613_);
v___x_4646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4646_, 0, v_v_4614_);
return v___x_4646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4647_, lean_object* v_v_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4647_, v_v_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4656_, lean_object* v_f_4657_, lean_object* v_v_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v___x_4665_; 
v___x_4665_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4657_, v_v_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4666_, lean_object* v_f_4667_, lean_object* v_v_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
uint8_t v_pu_boxed_4675_; lean_object* v_res_4676_; 
v_pu_boxed_4675_ = lean_unbox(v_pu_4666_);
v_res_4676_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4675_, v_f_4667_, v_v_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
return v_res_4676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v_toSignature_4685_; lean_object* v_value_4686_; uint8_t v_recursive_4687_; lean_object* v_inlineAttr_x3f_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4758_; 
v_toSignature_4685_ = lean_ctor_get(v_decl_4678_, 0);
v_value_4686_ = lean_ctor_get(v_decl_4678_, 1);
v_recursive_4687_ = lean_ctor_get_uint8(v_decl_4678_, sizeof(void*)*3);
v_inlineAttr_x3f_4688_ = lean_ctor_get(v_decl_4678_, 2);
v_isSharedCheck_4758_ = !lean_is_exclusive(v_decl_4678_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4690_ = v_decl_4678_;
v_isShared_4691_ = v_isSharedCheck_4758_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_inlineAttr_x3f_4688_);
lean_inc(v_value_4686_);
lean_inc(v_toSignature_4685_);
lean_dec(v_decl_4678_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4758_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v_name_4692_; lean_object* v_type_4693_; lean_object* v_params_4694_; uint8_t v_safe_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4756_; 
v_name_4692_ = lean_ctor_get(v_toSignature_4685_, 0);
v_type_4693_ = lean_ctor_get(v_toSignature_4685_, 2);
v_params_4694_ = lean_ctor_get(v_toSignature_4685_, 3);
v_safe_4695_ = lean_ctor_get_uint8(v_toSignature_4685_, sizeof(void*)*4);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_toSignature_4685_);
if (v_isSharedCheck_4756_ == 0)
{
lean_object* v_unused_4757_; 
v_unused_4757_ = lean_ctor_get(v_toSignature_4685_, 1);
lean_dec(v_unused_4757_);
v___x_4697_ = v_toSignature_4685_;
v_isShared_4698_ = v_isSharedCheck_4756_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_params_4694_);
lean_inc(v_type_4693_);
lean_inc(v_name_4692_);
lean_dec(v_toSignature_4685_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4756_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4699_; 
v___x_4699_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4693_, v_a_4682_, v_a_4683_);
if (lean_obj_tag(v___x_4699_) == 0)
{
lean_object* v_a_4700_; size_t v_sz_4701_; size_t v___x_4702_; lean_object* v___x_4703_; 
v_a_4700_ = lean_ctor_get(v___x_4699_, 0);
lean_inc(v_a_4700_);
lean_dec_ref_known(v___x_4699_, 1);
v_sz_4701_ = lean_array_size(v_params_4694_);
v___x_4702_ = ((size_t)0ULL);
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4701_, v___x_4702_, v_params_4694_, v_a_4679_, v_a_4681_, v_a_4682_, v_a_4683_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___f_4705_; lean_object* v___x_4706_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4704_);
lean_dec_ref_known(v___x_4703_, 1);
v___f_4705_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4706_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4705_, v_value_4686_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4708_; lean_object* v___x_4710_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
v___x_4708_ = lean_box(0);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 3, v_a_4704_);
lean_ctor_set(v___x_4697_, 2, v_a_4700_);
lean_ctor_set(v___x_4697_, 1, v___x_4708_);
v___x_4710_ = v___x_4697_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v_name_4692_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v___x_4708_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_a_4700_);
lean_ctor_set(v_reuseFailAlloc_4731_, 3, v_a_4704_);
lean_ctor_set_uint8(v_reuseFailAlloc_4731_, sizeof(void*)*4, v_safe_4695_);
v___x_4710_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
lean_object* v___x_4712_; 
if (v_isShared_4691_ == 0)
{
lean_ctor_set(v___x_4690_, 1, v_a_4707_);
lean_ctor_set(v___x_4690_, 0, v___x_4710_);
v___x_4712_ = v___x_4690_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_a_4707_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_inlineAttr_x3f_4688_);
lean_ctor_set_uint8(v_reuseFailAlloc_4730_, sizeof(void*)*3, v_recursive_4687_);
v___x_4712_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; 
lean_inc_ref(v___x_4712_);
v___x_4713_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4712_, v_a_4683_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; 
v_unused_4721_ = lean_ctor_get(v___x_4713_, 0);
lean_dec(v_unused_4721_);
v___x_4715_ = v___x_4713_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_dec(v___x_4713_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v___x_4712_);
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v___x_4712_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec_ref(v___x_4712_);
v_a_4722_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4713_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4713_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec(v_a_4704_);
lean_dec(v_a_4700_);
lean_del_object(v___x_4697_);
lean_dec(v_name_4692_);
lean_del_object(v___x_4690_);
lean_dec(v_inlineAttr_x3f_4688_);
v_a_4732_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4706_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4706_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
else
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4747_; 
lean_dec(v_a_4700_);
lean_del_object(v___x_4697_);
lean_dec(v_name_4692_);
lean_del_object(v___x_4690_);
lean_dec(v_inlineAttr_x3f_4688_);
lean_dec_ref(v_value_4686_);
v_a_4740_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4742_ = v___x_4703_;
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4703_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4747_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4745_; 
if (v_isShared_4743_ == 0)
{
v___x_4745_ = v___x_4742_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
lean_del_object(v___x_4697_);
lean_dec_ref(v_params_4694_);
lean_dec(v_name_4692_);
lean_del_object(v___x_4690_);
lean_dec(v_inlineAttr_x3f_4688_);
lean_dec_ref(v_value_4686_);
v_a_4748_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4699_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4699_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4759_, v_a_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
lean_dec(v_a_4762_);
lean_dec_ref(v_a_4761_);
lean_dec(v_a_4760_);
return v_res_4766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4773_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4774_ = lean_st_mk_ref(v___x_4773_);
v___x_4775_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4767_, v___x_4774_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4784_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4778_ = v___x_4775_;
v_isShared_4779_ = v_isSharedCheck_4784_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___x_4775_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4784_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4780_; lean_object* v___x_4782_; 
v___x_4780_ = lean_st_ref_get(v___x_4774_);
lean_dec(v___x_4774_);
lean_dec(v___x_4780_);
if (v_isShared_4779_ == 0)
{
v___x_4782_ = v___x_4778_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4776_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
else
{
lean_dec(v___x_4774_);
return v___x_4775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v_res_4791_; 
v_res_4791_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4785_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
lean_dec(v_a_4789_);
lean_dec_ref(v_a_4788_);
lean_dec(v_a_4787_);
lean_dec_ref(v_a_4786_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4792_, size_t v_i_4793_, lean_object* v_bs_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
uint8_t v___x_4800_; 
v___x_4800_ = lean_usize_dec_lt(v_i_4793_, v_sz_4792_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; 
v___x_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4801_, 0, v_bs_4794_);
return v___x_4801_;
}
else
{
lean_object* v_v_4802_; lean_object* v___x_4803_; 
v_v_4802_ = lean_array_uget_borrowed(v_bs_4794_, v_i_4793_);
lean_inc(v_v_4802_);
v___x_4803_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4802_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; lean_object* v_bs_x27_4806_; size_t v___x_4807_; size_t v___x_4808_; lean_object* v___x_4809_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4805_ = lean_unsigned_to_nat(0u);
v_bs_x27_4806_ = lean_array_uset(v_bs_4794_, v_i_4793_, v___x_4805_);
v___x_4807_ = ((size_t)1ULL);
v___x_4808_ = lean_usize_add(v_i_4793_, v___x_4807_);
v___x_4809_ = lean_array_uset(v_bs_x27_4806_, v_i_4793_, v_a_4804_);
v_i_4793_ = v___x_4808_;
v_bs_4794_ = v___x_4809_;
goto _start;
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec_ref(v_bs_4794_);
v_a_4811_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4803_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4803_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4819_, lean_object* v_i_4820_, lean_object* v_bs_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
size_t v_sz_boxed_4827_; size_t v_i_boxed_4828_; lean_object* v_res_4829_; 
v_sz_boxed_4827_ = lean_unbox_usize(v_sz_4819_);
lean_dec(v_sz_4819_);
v_i_boxed_4828_ = lean_unbox_usize(v_i_4820_);
lean_dec(v_i_4820_);
v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4827_, v_i_boxed_4828_, v_bs_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
lean_dec(v___y_4825_);
lean_dec_ref(v___y_4824_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
size_t v_sz_4836_; size_t v___x_4837_; lean_object* v___x_4838_; 
v_sz_4836_ = lean_array_size(v_x_4830_);
v___x_4837_ = ((size_t)0ULL);
v___x_4838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4836_, v___x_4837_, v_x_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v_res_4845_; 
v_res_4845_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
lean_dec(v___y_4841_);
lean_dec_ref(v___y_4840_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4928_; uint8_t v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v___x_4928_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4929_ = 1;
v___x_4930_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4931_ = l_Lean_registerTraceClass(v___x_4928_, v___x_4929_, v___x_4930_);
return v___x_4931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4933_;
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
