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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_fvarId_435_; uint8_t v___x_436_; uint8_t v___x_437_; 
v___x_433_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_434_ = lean_array_get_borrowed(v___x_433_, v_params_429_, v_a_431_);
v_fvarId_435_ = lean_ctor_get(v___x_434_, 0);
v___x_436_ = l_Lean_instBEqFVarId_beq(v_fvarId_435_, v_fvarId_430_);
v___x_437_ = lean_bool_not(v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v_a_431_);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_a_431_, v___x_439_);
lean_dec(v_a_431_);
v_a_431_ = v___x_440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___boxed(lean_object* v_params_442_, lean_object* v_fvarId_443_, lean_object* v_a_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_442_, v_fvarId_443_, v_a_444_);
lean_dec(v_fvarId_443_);
lean_dec_ref(v_params_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(lean_object* v_params_447_, lean_object* v_args_448_, lean_object* v_as_449_, size_t v_sz_450_, size_t v_i_451_, lean_object* v_b_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_a_460_; uint8_t v___x_464_; 
v___x_464_ = lean_usize_dec_lt(v_i_451_, v_sz_450_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v_b_452_);
return v___x_465_;
}
else
{
lean_object* v_fst_466_; lean_object* v_snd_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_499_; 
v_fst_466_ = lean_ctor_get(v_b_452_, 0);
v_snd_467_ = lean_ctor_get(v_b_452_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_b_452_);
if (v_isSharedCheck_499_ == 0)
{
v___x_469_ = v_b_452_;
v_isShared_470_ = v_isSharedCheck_499_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_467_);
lean_inc(v_fst_466_);
lean_dec(v_b_452_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_499_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_a_471_; 
v_a_471_ = lean_array_uget_borrowed(v_as_449_, v_i_451_);
if (lean_obj_tag(v_a_471_) == 1)
{
lean_object* v_fvarId_472_; lean_object* v___x_473_; 
v_fvarId_472_ = lean_ctor_get(v_a_471_, 0);
v___x_473_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_447_, v_fvarId_472_, v_snd_467_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v_a_476_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v___x_483_ = lean_box(0);
v___x_484_ = lean_array_get_borrowed(v___x_483_, v_args_448_, v_a_474_);
if (lean_obj_tag(v___x_484_) == 1)
{
lean_object* v_fvarId_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_fvarId_485_ = lean_ctor_get(v___x_484_, 0);
v___x_486_ = lean_st_ref_get(v___y_453_);
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_486_, v_fvarId_485_);
lean_dec(v___x_486_);
if (v___x_487_ == 0)
{
lean_inc_ref(v___x_484_);
v_a_476_ = v___x_484_;
goto v___jp_475_;
}
else
{
v_a_476_ = v___x_483_;
goto v___jp_475_;
}
}
else
{
v_a_476_ = v___x_483_;
goto v___jp_475_;
}
v___jp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v_a_474_, v___x_477_);
lean_dec(v_a_474_);
v___x_479_ = lean_array_push(v_fst_466_, v_a_476_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 1, v___x_478_);
lean_ctor_set(v___x_469_, 0, v___x_479_);
v___x_481_ = v___x_469_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_478_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
v_a_460_ = v___x_481_;
goto v___jp_459_;
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_del_object(v___x_469_);
lean_dec(v_fst_466_);
v_a_488_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_473_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_473_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_497_; 
if (v_isShared_470_ == 0)
{
v___x_497_ = v___x_469_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_fst_466_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_snd_467_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
v_a_460_ = v___x_497_;
goto v___jp_459_;
}
}
}
}
v___jp_459_:
{
size_t v___x_461_; size_t v___x_462_; 
v___x_461_ = ((size_t)1ULL);
v___x_462_ = lean_usize_add(v_i_451_, v___x_461_);
v_i_451_ = v___x_462_;
v_b_452_ = v_a_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1___boxed(lean_object* v_params_500_, lean_object* v_args_501_, lean_object* v_as_502_, lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_b_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
size_t v_sz_boxed_512_; size_t v_i_boxed_513_; lean_object* v_res_514_; 
v_sz_boxed_512_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_513_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(v_params_500_, v_args_501_, v_as_502_, v_sz_boxed_512_, v_i_boxed_513_, v_b_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v_as_502_);
lean_dec_ref(v_args_501_);
lean_dec_ref(v_params_500_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg(lean_object* v_args_520_, lean_object* v_params_521_, lean_object* v_redArgs_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; size_t v_sz_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1));
v_sz_531_ = lean_array_size(v_redArgs_522_);
v___x_532_ = ((size_t)0ULL);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(v_params_521_, v_args_520_, v_redArgs_522_, v_sz_531_, v___x_532_, v___x_530_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_object* v_a_534_; lean_object* v_fst_535_; lean_object* v_lower_537_; lean_object* v_upper_538_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_a_534_ = lean_ctor_get(v___x_533_, 0);
lean_inc(v_a_534_);
lean_dec_ref_known(v___x_533_, 1);
v_fst_535_ = lean_ctor_get(v_a_534_, 0);
lean_inc(v_fst_535_);
lean_dec(v_a_534_);
v___x_541_ = lean_array_get_size(v_params_521_);
v___x_542_ = lean_array_get_size(v_args_520_);
v___x_543_ = lean_nat_dec_le(v___x_541_, v___x_529_);
if (v___x_543_ == 0)
{
v_lower_537_ = v___x_541_;
v_upper_538_ = v___x_542_;
goto v___jp_536_;
}
else
{
v_lower_537_ = v___x_529_;
v_upper_538_ = v___x_542_;
goto v___jp_536_;
}
v___jp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = l_Array_toSubarray___redArg(v_args_520_, v_lower_537_, v_upper_538_);
v___x_540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v___x_539_, v_fst_535_, v_a_523_);
return v___x_540_;
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_args_520_);
v_a_544_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_533_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_533_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___boxed(lean_object* v_args_552_, lean_object* v_params_553_, lean_object* v_redArgs_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_552_, v_params_553_, v_redArgs_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_redArgs_554_);
lean_dec_ref(v_params_553_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(lean_object* v_params_562_, lean_object* v_fvarId_563_, lean_object* v_inst_564_, lean_object* v_a_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_562_, v_fvarId_563_, v_a_565_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___boxed(lean_object* v_params_573_, lean_object* v_fvarId_574_, lean_object* v_inst_575_, lean_object* v_a_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(v_params_573_, v_fvarId_574_, v_inst_575_, v_a_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec(v_fvarId_574_);
lean_dec_ref(v_params_573_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(lean_object* v_inst_584_, lean_object* v_R_585_, lean_object* v_a_586_, lean_object* v_b_587_, lean_object* v_c_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v_a_586_, v_b_587_, v___y_589_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___boxed(lean_object* v_inst_596_, lean_object* v_R_597_, lean_object* v_a_598_, lean_object* v_b_599_, lean_object* v_c_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(v_inst_596_, v_R_597_, v_a_598_, v_b_599_, v_c_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object* v_a_608_, lean_object* v_b_609_){
_start:
{
lean_object* v_array_610_; lean_object* v_start_611_; lean_object* v_stop_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_625_; 
v_array_610_ = lean_ctor_get(v_a_608_, 0);
v_start_611_ = lean_ctor_get(v_a_608_, 1);
v_stop_612_ = lean_ctor_get(v_a_608_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_625_ == 0)
{
v___x_614_ = v_a_608_;
v_isShared_615_ = v_isSharedCheck_625_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_stop_612_);
lean_inc(v_start_611_);
lean_inc(v_array_610_);
lean_dec(v_a_608_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_625_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v_start_611_, v_stop_612_);
if (v___x_616_ == 0)
{
lean_del_object(v___x_614_);
lean_dec(v_stop_612_);
lean_dec(v_start_611_);
lean_dec_ref(v_array_610_);
return v_b_609_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_start_611_, v___x_617_);
lean_inc_ref(v_array_610_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_618_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_array_610_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_stop_612_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_array_fget(v_array_610_, v_start_611_);
lean_dec(v_start_611_);
lean_dec_ref(v_array_610_);
v___x_622_ = lean_array_push(v_b_609_, v___x_621_);
v_a_608_ = v___x_620_;
v_b_609_ = v___x_622_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t v_sz_626_, size_t v_i_627_, lean_object* v_bs_628_, lean_object* v___y_629_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_lt(v_i_627_, v_sz_626_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_bs_628_);
return v___x_632_;
}
else
{
lean_object* v_v_633_; lean_object* v___x_634_; lean_object* v_bs_x27_635_; lean_object* v_a_637_; 
v_v_633_ = lean_array_uget(v_bs_628_, v_i_627_);
v___x_634_ = lean_unsigned_to_nat(0u);
v_bs_x27_635_ = lean_array_uset(v_bs_628_, v_i_627_, v___x_634_);
if (lean_obj_tag(v_v_633_) == 1)
{
lean_object* v_fvarId_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_fvarId_642_ = lean_ctor_get(v_v_633_, 0);
v___x_643_ = lean_st_ref_get(v___y_629_);
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_643_, v_fvarId_642_);
lean_dec(v___x_643_);
if (v___x_644_ == 0)
{
v_a_637_ = v_v_633_;
goto v___jp_636_;
}
else
{
lean_object* v___x_645_; 
lean_dec_ref_known(v_v_633_, 1);
v___x_645_ = lean_box(0);
v_a_637_ = v___x_645_;
goto v___jp_636_;
}
}
else
{
lean_object* v___x_646_; 
lean_dec(v_v_633_);
v___x_646_ = lean_box(0);
v_a_637_ = v___x_646_;
goto v___jp_636_;
}
v___jp_636_:
{
size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_add(v_i_627_, v___x_638_);
v___x_640_ = lean_array_uset(v_bs_x27_635_, v_i_627_, v_a_637_);
v_i_627_ = v___x_639_;
v_bs_628_ = v___x_640_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object* v_sz_647_, lean_object* v_i_648_, lean_object* v_bs_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
size_t v_sz_boxed_652_; size_t v_i_boxed_653_; lean_object* v_res_654_; 
v_sz_boxed_652_ = lean_unbox_usize(v_sz_647_);
lean_dec(v_sz_647_);
v_i_boxed_653_ = lean_unbox_usize(v_i_648_);
lean_dec(v_i_648_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_boxed_652_, v_i_boxed_653_, v_bs_649_, v___y_650_);
lean_dec(v___y_650_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object* v_ctorInfo_655_, lean_object* v_args_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_toConstantVal_663_; lean_object* v_numParams_664_; lean_object* v___x_665_; lean_object* v_argsNewParams_666_; lean_object* v_lower_668_; lean_object* v_upper_669_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_toConstantVal_663_ = lean_ctor_get(v_ctorInfo_655_, 0);
lean_inc_ref(v_toConstantVal_663_);
v_numParams_664_ = lean_ctor_get(v_ctorInfo_655_, 3);
lean_inc_n(v_numParams_664_, 2);
lean_dec_ref(v_ctorInfo_655_);
v___x_665_ = lean_box(0);
v_argsNewParams_666_ = lean_mk_array(v_numParams_664_, v___x_665_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_array_get_size(v_args_656_);
v___x_706_ = lean_nat_dec_le(v_numParams_664_, v___x_704_);
if (v___x_706_ == 0)
{
v_lower_668_ = v_numParams_664_;
v_upper_669_ = v___x_705_;
goto v___jp_667_;
}
else
{
lean_dec(v_numParams_664_);
v_lower_668_ = v___x_704_;
v_upper_669_ = v___x_705_;
goto v___jp_667_;
}
v___jp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; size_t v_sz_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_670_ = l_Array_toSubarray___redArg(v_args_656_, v_lower_668_, v_upper_669_);
v___x_671_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_672_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v___x_670_, v___x_671_);
v_sz_673_ = lean_array_size(v___x_672_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_673_, v___x_674_, v___x_672_, v_a_657_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_695_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_695_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_695_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_695_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_name_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_692_; 
v_name_680_ = lean_ctor_get(v_toConstantVal_663_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v_toConstantVal_663_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; lean_object* v_unused_694_; 
v_unused_693_ = lean_ctor_get(v_toConstantVal_663_, 2);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v_toConstantVal_663_, 1);
lean_dec(v_unused_694_);
v___x_682_ = v_toConstantVal_663_;
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_name_680_);
lean_dec(v_toConstantVal_663_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_692_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_684_ = l_Array_append___redArg(v_argsNewParams_666_, v_a_676_);
lean_dec(v_a_676_);
v___x_685_ = lean_box(0);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 3);
lean_ctor_set(v___x_682_, 2, v___x_684_);
lean_ctor_set(v___x_682_, 1, v___x_685_);
v___x_687_ = v___x_682_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_name_680_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_691_, 2, v___x_684_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_689_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_687_);
v___x_689_ = v___x_678_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v_argsNewParams_666_);
lean_dec_ref(v_toConstantVal_663_);
v_a_696_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_675_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_675_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object* v_ctorInfo_707_, lean_object* v_args_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_ctorInfo_707_, v_args_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0(lean_object* v_inst_716_, lean_object* v_R_717_, lean_object* v_a_718_, lean_object* v_b_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v_a_718_, v_b_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t v_sz_721_, size_t v_i_722_, lean_object* v_bs_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_721_, v_i_722_, v_bs_723_, v___y_724_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object* v_sz_731_, lean_object* v_i_732_, lean_object* v_bs_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
size_t v_sz_boxed_740_; size_t v_i_boxed_741_; lean_object* v_res_742_; 
v_sz_boxed_740_ = lean_unbox_usize(v_sz_731_);
lean_dec(v_sz_731_);
v_i_boxed_741_ = lean_unbox_usize(v_i_732_);
lean_dec(v_i_732_);
v_res_742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(v_sz_boxed_740_, v_i_boxed_741_, v_bs_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
return v_res_742_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_instMonadEIO(lean_box(0));
return v___x_743_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5(void){
_start:
{
uint8_t v___x_748_; lean_object* v___x_749_; 
v___x_748_ = 0;
v___x_749_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object* v_msg_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_toApplicative_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_821_; 
v___x_757_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_758_ = l_StateRefT_x27_instMonad___redArg(v___x_757_);
v_toApplicative_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_758_, 1);
lean_dec(v_unused_822_);
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_821_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_toApplicative_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_821_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_toFunctor_763_; lean_object* v_toSeq_764_; lean_object* v_toSeqLeft_765_; lean_object* v_toSeqRight_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_819_; 
v_toFunctor_763_ = lean_ctor_get(v_toApplicative_759_, 0);
v_toSeq_764_ = lean_ctor_get(v_toApplicative_759_, 2);
v_toSeqLeft_765_ = lean_ctor_get(v_toApplicative_759_, 3);
v_toSeqRight_766_ = lean_ctor_get(v_toApplicative_759_, 4);
v_isSharedCheck_819_ = !lean_is_exclusive(v_toApplicative_759_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_toApplicative_759_, 1);
lean_dec(v_unused_820_);
v___x_768_ = v_toApplicative_759_;
v_isShared_769_ = v_isSharedCheck_819_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_toSeqRight_766_);
lean_inc(v_toSeqLeft_765_);
lean_inc(v_toSeq_764_);
lean_inc(v_toFunctor_763_);
lean_dec(v_toApplicative_759_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_819_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___x_779_; 
v___f_770_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_771_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_763_);
v___f_772_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_772_, 0, v_toFunctor_763_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_773_, 0, v_toFunctor_763_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___f_772_);
lean_ctor_set(v___x_774_, 1, v___f_773_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_775_, 0, v_toSeqRight_766_);
v___f_776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_776_, 0, v_toSeqLeft_765_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeq_764_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 4, v___f_775_);
lean_ctor_set(v___x_768_, 3, v___f_776_);
lean_ctor_set(v___x_768_, 2, v___f_777_);
lean_ctor_set(v___x_768_, 1, v___f_770_);
lean_ctor_set(v___x_768_, 0, v___x_774_);
v___x_779_ = v___x_768_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___f_770_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v___f_777_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___f_776_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v___f_775_);
v___x_779_ = v_reuseFailAlloc_818_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___f_771_);
lean_ctor_set(v___x_761_, 0, v___x_779_);
v___x_781_ = v___x_761_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___f_771_);
v___x_781_ = v_reuseFailAlloc_817_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v_toApplicative_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_815_; 
v___x_782_ = l_StateRefT_x27_instMonad___redArg(v___x_781_);
v_toApplicative_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_782_, 1);
lean_dec(v_unused_816_);
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_815_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_toApplicative_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_815_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_toFunctor_787_; lean_object* v_toSeq_788_; lean_object* v_toSeqLeft_789_; lean_object* v_toSeqRight_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_813_; 
v_toFunctor_787_ = lean_ctor_get(v_toApplicative_783_, 0);
v_toSeq_788_ = lean_ctor_get(v_toApplicative_783_, 2);
v_toSeqLeft_789_ = lean_ctor_get(v_toApplicative_783_, 3);
v_toSeqRight_790_ = lean_ctor_get(v_toApplicative_783_, 4);
v_isSharedCheck_813_ = !lean_is_exclusive(v_toApplicative_783_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_toApplicative_783_, 1);
lean_dec(v_unused_814_);
v___x_792_ = v_toApplicative_783_;
v_isShared_793_ = v_isSharedCheck_813_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_toSeqRight_790_);
lean_inc(v_toSeqLeft_789_);
lean_inc(v_toSeq_788_);
lean_inc(v_toFunctor_787_);
lean_dec(v_toApplicative_783_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_813_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___x_803_; 
v___f_794_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_795_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_787_);
v___f_796_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_796_, 0, v_toFunctor_787_);
v___f_797_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_797_, 0, v_toFunctor_787_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___f_796_);
lean_ctor_set(v___x_798_, 1, v___f_797_);
v___f_799_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_799_, 0, v_toSeqRight_790_);
v___f_800_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_800_, 0, v_toSeqLeft_789_);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_801_, 0, v_toSeq_788_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v___f_799_);
lean_ctor_set(v___x_792_, 3, v___f_800_);
lean_ctor_set(v___x_792_, 2, v___f_801_);
lean_ctor_set(v___x_792_, 1, v___f_794_);
lean_ctor_set(v___x_792_, 0, v___x_798_);
v___x_803_ = v___x_792_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___f_794_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v___f_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v___f_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v___f_799_);
v___x_803_ = v_reuseFailAlloc_812_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___f_795_);
lean_ctor_set(v___x_785_, 0, v___x_803_);
v___x_805_ = v___x_785_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___f_795_);
v___x_805_ = v_reuseFailAlloc_811_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_13669__overap_809_; lean_object* v___x_810_; 
v___x_806_ = l_StateRefT_x27_instMonad___redArg(v___x_805_);
v___x_807_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_808_ = l_instInhabitedOfMonad___redArg(v___x_806_, v___x_807_);
v___x_13669__overap_809_ = lean_panic_fn_borrowed(v___x_808_, v_msg_750_);
lean_dec(v___x_808_);
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
v___x_810_ = lean_apply_6(v___x_13669__overap_809_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, lean_box(0));
return v___x_810_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object* v_upperBound_831_, lean_object* v_args_832_, lean_object* v_a_833_, lean_object* v_b_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_a_838_; uint8_t v___x_843_; 
v___x_843_ = lean_nat_dec_lt(v_a_833_, v_upperBound_831_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v_a_833_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_834_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_box(0);
v___x_846_ = lean_array_get_borrowed(v___x_845_, v_args_832_, v_a_833_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_fvarId_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_fvarId_847_ = lean_ctor_get(v___x_846_, 0);
v___x_848_ = lean_st_ref_get(v___y_835_);
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_848_, v_fvarId_847_);
lean_dec(v___x_848_);
if (v___x_849_ == 0)
{
lean_inc_ref(v___x_846_);
v_a_838_ = v___x_846_;
goto v___jp_837_;
}
else
{
v_a_838_ = v___x_845_;
goto v___jp_837_;
}
}
else
{
v_a_838_ = v___x_845_;
goto v___jp_837_;
}
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_array_push(v_b_834_, v_a_838_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_a_833_, v___x_840_);
lean_dec(v_a_833_);
v_a_833_ = v___x_841_;
v_b_834_ = v___x_839_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object* v_upperBound_850_, lean_object* v_args_851_, lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_850_, v_args_851_, v_a_852_, v_b_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v_args_851_);
lean_dec(v_upperBound_850_);
return v_res_856_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__22(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_894_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_895_ = lean_unsigned_to_nat(6u);
v___x_896_ = lean_unsigned_to_nat(109u);
v___x_897_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__20));
v___x_898_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_899_ = l_mkPanicMessageWithDecl(v___x_898_, v___x_897_, v___x_896_, v___x_895_, v___x_894_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
switch(lean_obj_tag(v_e_921_))
{
case 2:
{
lean_object* v_typeName_928_; lean_object* v_idx_929_; lean_object* v_struct_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_typeName_928_ = lean_ctor_get(v_e_921_, 0);
v_idx_929_ = lean_ctor_get(v_e_921_, 1);
v_struct_930_ = lean_ctor_get(v_e_921_, 2);
v___x_931_ = lean_st_ref_get(v_a_922_);
v___x_932_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_931_, v_struct_930_);
lean_dec(v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; 
lean_inc(v_typeName_928_);
v___x_933_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_928_, v_a_925_, v_a_926_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_953_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_953_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_953_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_953_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
if (lean_obj_tag(v_a_934_) == 1)
{
lean_object* v_val_938_; lean_object* v_fieldIdx_939_; uint8_t v___x_940_; 
lean_inc(v_struct_930_);
lean_inc(v_idx_929_);
lean_dec_ref_known(v_e_921_, 3);
v_val_938_ = lean_ctor_get(v_a_934_, 0);
lean_inc(v_val_938_);
lean_dec_ref_known(v_a_934_, 1);
v_fieldIdx_939_ = lean_ctor_get(v_val_938_, 2);
lean_inc(v_fieldIdx_939_);
lean_dec(v_val_938_);
v___x_940_ = lean_nat_dec_eq(v_fieldIdx_939_, v_idx_929_);
lean_dec(v_idx_929_);
lean_dec(v_fieldIdx_939_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_943_; 
lean_dec(v_struct_930_);
v___x_941_ = lean_box(1);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_941_);
v___x_943_ = v___x_936_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_946_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_946_, 0, v_struct_930_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_946_);
v___x_948_ = v___x_936_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v___x_951_; 
lean_dec(v_a_934_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_e_921_);
v___x_951_ = v___x_936_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_e_921_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref_known(v_e_921_, 3);
v_a_954_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_933_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_933_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec_ref_known(v_e_921_, 3);
v___x_962_ = lean_box(1);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
return v___x_963_;
}
}
case 3:
{
lean_object* v_declName_964_; lean_object* v_args_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1172_; 
v_declName_964_ = lean_ctor_get(v_e_921_, 0);
v_args_965_ = lean_ctor_get(v_e_921_, 2);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_e_921_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; 
v_unused_1173_ = lean_ctor_get(v_e_921_, 1);
lean_dec(v_unused_1173_);
v___x_967_ = v_e_921_;
v_isShared_968_ = v_isSharedCheck_1172_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_args_965_);
lean_inc(v_declName_964_);
lean_dec(v_e_921_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1172_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_type_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; uint8_t v___y_1007_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1033_; lean_object* v___y_1034_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_1088_ = lean_name_eq(v_declName_964_, v___x_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__6));
v___x_1090_ = lean_name_eq(v_declName_964_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_1092_ = lean_name_eq(v_declName_964_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_1094_ = lean_name_eq(v_declName_964_, v___x_1093_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__13));
v___x_1096_ = lean_name_eq(v_declName_964_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__16));
v___x_1098_ = lean_name_eq(v_declName_964_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_1100_ = lean_name_eq(v_declName_964_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v_env_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_st_ref_get(v_a_926_);
v_env_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc_ref(v_env_1102_);
lean_dec(v___x_1101_);
lean_inc(v_declName_964_);
v___x_1103_ = l_Lean_Environment_find_x3f(v_env_1102_, v_declName_964_, v___x_1100_);
if (lean_obj_tag(v___x_1103_) == 1)
{
lean_object* v_val_1104_; 
v_val_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v___x_1103_, 1);
if (lean_obj_tag(v_val_1104_) == 6)
{
lean_object* v_val_1105_; lean_object* v_induct_1106_; lean_object* v_numParams_1107_; lean_object* v___x_1108_; 
lean_del_object(v___x_967_);
lean_dec(v_declName_964_);
v_val_1105_ = lean_ctor_get(v_val_1104_, 0);
lean_inc_ref(v_val_1105_);
lean_dec_ref_known(v_val_1104_, 1);
v_induct_1106_ = lean_ctor_get(v_val_1105_, 1);
v_numParams_1107_ = lean_ctor_get(v_val_1105_, 3);
lean_inc(v_induct_1106_);
v___x_1108_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_1106_, v_a_925_, v_a_926_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
lean_dec_ref_known(v___x_1108_, 1);
if (lean_obj_tag(v_a_1109_) == 1)
{
lean_object* v_val_1110_; lean_object* v_fieldIdx_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc(v_numParams_1107_);
lean_dec_ref(v_val_1105_);
v_val_1110_ = lean_ctor_get(v_a_1109_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v_a_1109_, 1);
v_fieldIdx_1111_ = lean_ctor_get(v_val_1110_, 2);
lean_inc(v_fieldIdx_1111_);
lean_dec(v_val_1110_);
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_nat_add(v_numParams_1107_, v_fieldIdx_1111_);
lean_dec(v_fieldIdx_1111_);
lean_dec(v_numParams_1107_);
v___x_1114_ = lean_array_get(v___x_1112_, v_args_965_, v___x_1113_);
lean_dec(v___x_1113_);
lean_dec_ref(v_args_965_);
v___x_1115_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1114_);
lean_dec(v___x_1114_);
v_e_921_ = v___x_1115_;
goto _start;
}
else
{
lean_object* v___x_1117_; 
lean_dec(v_a_1109_);
v___x_1117_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_1105_, v_args_965_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_1117_;
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_val_1105_);
lean_dec_ref(v_args_965_);
v_a_1118_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1108_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1108_);
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
lean_dec(v_val_1104_);
v___y_1030_ = v_a_922_;
v___y_1031_ = v_a_923_;
v___y_1032_ = v_a_924_;
v___y_1033_ = v_a_925_;
v___y_1034_ = v_a_926_;
goto v___jp_1029_;
}
}
else
{
lean_dec(v___x_1103_);
v___y_1030_ = v_a_922_;
v___y_1031_ = v_a_923_;
v___y_1032_ = v_a_924_;
v___y_1033_ = v_a_925_;
v___y_1034_ = v_a_926_;
goto v___jp_1029_;
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_del_object(v___x_967_);
lean_dec_ref(v_args_965_);
lean_dec(v_declName_964_);
v___x_1126_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__22, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__22_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__22);
v___x_1127_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_1126_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_1127_;
}
}
else
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_967_);
lean_dec_ref(v_args_965_);
lean_dec(v_declName_964_);
v___x_1128_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_967_);
lean_dec(v_declName_964_);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_unsigned_to_nat(2u);
v___x_1132_ = lean_array_get_borrowed(v___x_1130_, v_args_965_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 1)
{
lean_object* v_fvarId_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_extraArgs_1137_; lean_object* v___x_1138_; 
v_fvarId_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_fvarId_1133_);
v___x_1134_ = lean_array_get_size(v_args_965_);
v___x_1135_ = lean_unsigned_to_nat(3u);
v___x_1136_ = lean_nat_sub(v___x_1134_, v___x_1135_);
v_extraArgs_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
lean_dec(v___x_1136_);
v___x_1138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_1134_, v_args_965_, v___x_1135_, v_extraArgs_1137_, v_a_922_);
lean_dec_ref(v_args_965_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1143_, 0, v_fvarId_1133_);
lean_ctor_set(v___x_1143_, 1, v_a_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1145_ = v___x_1141_;
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
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_fvarId_1133_);
v_a_1148_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1138_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1138_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v_args_965_);
v___x_1156_ = lean_box(1);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
}
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_967_);
lean_dec(v_declName_964_);
v___x_1158_ = lean_box(0);
v___x_1159_ = lean_unsigned_to_nat(2u);
v___x_1160_ = lean_array_get(v___x_1158_, v_args_965_, v___x_1159_);
lean_dec_ref(v_args_965_);
v___x_1161_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
return v___x_1162_;
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
lean_del_object(v___x_967_);
lean_dec(v_declName_964_);
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_unsigned_to_nat(1u);
v___x_1165_ = lean_array_get(v___x_1163_, v_args_965_, v___x_1164_);
lean_dec_ref(v_args_965_);
v___x_1166_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1165_);
lean_dec(v___x_1165_);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_del_object(v___x_967_);
lean_dec_ref(v_args_965_);
lean_dec(v_declName_964_);
v___x_1168_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_del_object(v___x_967_);
lean_dec_ref(v_args_965_);
lean_dec(v_declName_964_);
v___x_1170_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__31));
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
v___jp_969_:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_965_, v_type_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec_ref(v_args_965_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_988_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_988_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_988_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_983_; 
v___x_981_ = lean_box(0);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 2, v_a_977_);
lean_ctor_set(v___x_967_, 1, v___x_981_);
v___x_983_ = v___x_967_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_declName_964_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_a_977_);
v___x_983_ = v_reuseFailAlloc_987_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_985_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_983_);
v___x_985_ = v___x_979_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
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
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_del_object(v___x_967_);
lean_dec(v_declName_964_);
v_a_989_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_976_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_976_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
v___jp_997_:
{
if (v___y_1007_ == 0)
{
lean_object* v_toSignature_1008_; lean_object* v_type_1009_; 
lean_dec_ref(v___y_1003_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_998_);
v_toSignature_1008_ = lean_ctor_get(v___y_1006_, 0);
lean_inc_ref(v_toSignature_1008_);
lean_dec_ref(v___y_1006_);
v_type_1009_ = lean_ctor_get(v_toSignature_1008_, 2);
lean_inc_ref(v_type_1009_);
lean_dec_ref(v_toSignature_1008_);
v_type_970_ = v_type_1009_;
v___y_971_ = v___y_1005_;
v___y_972_ = v___y_1004_;
v___y_973_ = v___y_1002_;
v___y_974_ = v___y_1001_;
v___y_975_ = v___y_999_;
goto v___jp_969_;
}
else
{
lean_object* v___x_1010_; 
lean_dec_ref(v___y_1006_);
lean_del_object(v___x_967_);
lean_dec(v_declName_964_);
v___x_1010_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_965_, v___y_1003_, v___y_1000_, v___y_1005_, v___y_1004_, v___y_1002_, v___y_1001_, v___y_999_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v___y_1003_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1020_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1020_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1016_, 0, v___y_998_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_ctor_set(v___x_1016_, 2, v_a_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1016_);
v___x_1018_ = v___x_1013_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v___y_998_);
v_a_1021_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1010_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1010_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
v___jp_1029_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_st_ref_get(v___y_1034_);
lean_dec(v___x_1035_);
lean_inc(v_declName_964_);
v___x_1036_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_964_, v___y_1034_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
if (lean_obj_tag(v_a_1037_) == 1)
{
lean_object* v_val_1038_; lean_object* v_toSignature_1039_; lean_object* v_value_1040_; lean_object* v_type_1041_; lean_object* v_params_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_val_1038_ = lean_ctor_get(v_a_1037_, 0);
lean_inc(v_val_1038_);
lean_dec_ref_known(v_a_1037_, 1);
v_toSignature_1039_ = lean_ctor_get(v_val_1038_, 0);
v_value_1040_ = lean_ctor_get(v_val_1038_, 1);
v_type_1041_ = lean_ctor_get(v_toSignature_1039_, 2);
v_params_1042_ = lean_ctor_get(v_toSignature_1039_, 3);
lean_inc_ref(v_params_1042_);
v___x_1043_ = lean_array_get_size(v_params_1042_);
v___x_1044_ = lean_array_get_size(v_args_965_);
v___x_1045_ = lean_nat_dec_le(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_inc_ref(v_type_1041_);
lean_dec_ref(v_params_1042_);
lean_dec(v_val_1038_);
v_type_970_ = v_type_1041_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
v___y_975_ = v___y_1034_;
goto v___jp_969_;
}
else
{
if (lean_obj_tag(v_value_1040_) == 0)
{
lean_object* v_code_1046_; 
v_code_1046_ = lean_ctor_get(v_value_1040_, 0);
if (lean_obj_tag(v_code_1046_) == 0)
{
lean_object* v_decl_1047_; lean_object* v_value_1048_; 
v_decl_1047_ = lean_ctor_get(v_code_1046_, 0);
v_value_1048_ = lean_ctor_get(v_decl_1047_, 3);
if (lean_obj_tag(v_value_1048_) == 3)
{
lean_object* v_k_1049_; 
v_k_1049_ = lean_ctor_get(v_code_1046_, 1);
if (lean_obj_tag(v_k_1049_) == 5)
{
lean_object* v_fvarId_1050_; lean_object* v_declName_1051_; lean_object* v_args_1052_; lean_object* v_fvarId_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_fvarId_1050_ = lean_ctor_get(v_decl_1047_, 0);
v_declName_1051_ = lean_ctor_get(v_value_1048_, 0);
v_args_1052_ = lean_ctor_get(v_value_1048_, 2);
lean_inc_ref(v_args_1052_);
v_fvarId_1053_ = lean_ctor_get(v_k_1049_, 0);
v___x_1054_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__1));
lean_inc(v_declName_964_);
v___x_1055_ = l_Lean_Name_append(v_declName_964_, v___x_1054_);
v___x_1056_ = lean_name_eq(v_declName_1051_, v___x_1055_);
if (v___x_1056_ == 0)
{
v___y_998_ = v___x_1055_;
v___y_999_ = v___y_1034_;
v___y_1000_ = v_args_1052_;
v___y_1001_ = v___y_1033_;
v___y_1002_ = v___y_1032_;
v___y_1003_ = v_params_1042_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v___y_1030_;
v___y_1006_ = v_val_1038_;
v___y_1007_ = v___x_1056_;
goto v___jp_997_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = l_Lean_instBEqFVarId_beq(v_fvarId_1053_, v_fvarId_1050_);
v___y_998_ = v___x_1055_;
v___y_999_ = v___y_1034_;
v___y_1000_ = v_args_1052_;
v___y_1001_ = v___y_1033_;
v___y_1002_ = v___y_1032_;
v___y_1003_ = v_params_1042_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v___y_1030_;
v___y_1006_ = v_val_1038_;
v___y_1007_ = v___x_1057_;
goto v___jp_997_;
}
}
else
{
lean_inc_ref(v_type_1041_);
lean_dec_ref(v_params_1042_);
lean_dec(v_val_1038_);
v_type_970_ = v_type_1041_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
v___y_975_ = v___y_1034_;
goto v___jp_969_;
}
}
else
{
lean_inc_ref(v_type_1041_);
lean_dec_ref(v_params_1042_);
lean_dec(v_val_1038_);
v_type_970_ = v_type_1041_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
v___y_975_ = v___y_1034_;
goto v___jp_969_;
}
}
else
{
lean_inc_ref(v_type_1041_);
lean_dec_ref(v_params_1042_);
lean_dec(v_val_1038_);
v_type_970_ = v_type_1041_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
v___y_975_ = v___y_1034_;
goto v___jp_969_;
}
}
else
{
lean_inc_ref(v_type_1041_);
lean_dec_ref(v_params_1042_);
lean_dec(v_val_1038_);
v_type_970_ = v_type_1041_;
v___y_971_ = v___y_1030_;
v___y_972_ = v___y_1031_;
v___y_973_ = v___y_1032_;
v___y_974_ = v___y_1033_;
v___y_975_ = v___y_1034_;
goto v___jp_969_;
}
}
}
else
{
size_t v_sz_1058_; size_t v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v_a_1037_);
lean_del_object(v___x_967_);
v_sz_1058_ = lean_array_size(v_args_965_);
v___x_1059_ = ((size_t)0ULL);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1058_, v___x_1059_, v_args_965_, v___y_1030_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1066_, 0, v_declName_964_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
lean_ctor_set(v___x_1066_, 2, v_a_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_declName_964_);
v_a_1071_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1060_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1060_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_967_);
lean_dec_ref(v_args_965_);
lean_dec(v_declName_964_);
v_a_1079_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1036_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1036_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_1174_; lean_object* v_args_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1205_; 
v_fvarId_1174_ = lean_ctor_get(v_e_921_, 0);
v_args_1175_ = lean_ctor_get(v_e_921_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_e_921_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1177_ = v_e_921_;
v_isShared_1178_ = v_isSharedCheck_1205_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_args_1175_);
lean_inc(v_fvarId_1174_);
lean_dec(v_e_921_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1205_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = lean_st_ref_get(v_a_922_);
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_1179_, v_fvarId_1174_);
lean_dec(v___x_1179_);
if (v___x_1180_ == 0)
{
size_t v_sz_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
v_sz_1181_ = lean_array_size(v_args_1175_);
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1181_, v___x_1182_, v_args_1175_, v_a_922_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1194_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1186_ = v___x_1183_;
v_isShared_1187_ = v_isSharedCheck_1194_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1194_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_a_1184_);
v___x_1189_ = v___x_1177_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_fvarId_1174_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1189_);
v___x_1191_ = v___x_1186_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_del_object(v___x_1177_);
lean_dec(v_fvarId_1174_);
v_a_1195_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1183_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1183_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
lean_del_object(v___x_1177_);
lean_dec_ref(v_args_1175_);
lean_dec(v_fvarId_1174_);
v___x_1203_ = lean_box(1);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
}
default: 
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_e_921_);
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_1215_, lean_object* v_args_1216_, lean_object* v_inst_1217_, lean_object* v_R_1218_, lean_object* v_a_1219_, lean_object* v_b_1220_, lean_object* v_c_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_1215_, v_args_1216_, v_a_1219_, v_b_1220_, v___y_1222_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_1229_, lean_object* v_args_1230_, lean_object* v_inst_1231_, lean_object* v_R_1232_, lean_object* v_a_1233_, lean_object* v_b_1234_, lean_object* v_c_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_1229_, v_args_1230_, v_inst_1231_, v_R_1232_, v_a_1233_, v_b_1234_, v_c_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v_args_1230_);
lean_dec(v_upperBound_1229_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_type_1250_; lean_object* v_value_1251_; lean_object* v___x_1252_; 
v_type_1250_ = lean_ctor_get(v_decl_1243_, 2);
v_value_1251_ = lean_ctor_get(v_decl_1243_, 3);
lean_inc_ref(v_type_1250_);
v___x_1252_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1250_, v_a_1247_, v_a_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1254_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
lean_inc(v_value_1251_);
v___x_1254_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_1251_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = 0;
v___x_1257_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1256_, v_decl_1243_, v_a_1253_, v_a_1255_, v_a_1246_);
return v___x_1257_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec(v_a_1253_);
lean_dec_ref(v_decl_1243_);
v_a_1258_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1254_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1254_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_decl_1243_);
v_a_1266_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1252_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1252_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_toApplicative_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1353_; 
v___x_1289_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1290_ = l_StateRefT_x27_instMonad___redArg(v___x_1289_);
v_toApplicative_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; 
v_unused_1354_ = lean_ctor_get(v___x_1290_, 1);
lean_dec(v_unused_1354_);
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1353_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_toApplicative_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1353_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_toFunctor_1295_; lean_object* v_toSeq_1296_; lean_object* v_toSeqLeft_1297_; lean_object* v_toSeqRight_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1351_; 
v_toFunctor_1295_ = lean_ctor_get(v_toApplicative_1291_, 0);
v_toSeq_1296_ = lean_ctor_get(v_toApplicative_1291_, 2);
v_toSeqLeft_1297_ = lean_ctor_get(v_toApplicative_1291_, 3);
v_toSeqRight_1298_ = lean_ctor_get(v_toApplicative_1291_, 4);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_toApplicative_1291_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v_toApplicative_1291_, 1);
lean_dec(v_unused_1352_);
v___x_1300_ = v_toApplicative_1291_;
v_isShared_1301_ = v_isSharedCheck_1351_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_toSeqRight_1298_);
lean_inc(v_toSeqLeft_1297_);
lean_inc(v_toSeq_1296_);
lean_inc(v_toFunctor_1295_);
lean_dec(v_toApplicative_1291_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1351_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___f_1305_; lean_object* v___x_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___x_1311_; 
v___f_1302_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1303_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1295_);
v___f_1304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1304_, 0, v_toFunctor_1295_);
v___f_1305_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1305_, 0, v_toFunctor_1295_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___f_1304_);
lean_ctor_set(v___x_1306_, 1, v___f_1305_);
v___f_1307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1307_, 0, v_toSeqRight_1298_);
v___f_1308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1308_, 0, v_toSeqLeft_1297_);
v___f_1309_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1309_, 0, v_toSeq_1296_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 4, v___f_1307_);
lean_ctor_set(v___x_1300_, 3, v___f_1308_);
lean_ctor_set(v___x_1300_, 2, v___f_1309_);
lean_ctor_set(v___x_1300_, 1, v___f_1302_);
lean_ctor_set(v___x_1300_, 0, v___x_1306_);
v___x_1311_ = v___x_1300_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v___f_1302_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v___f_1309_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v___f_1308_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v___f_1307_);
v___x_1311_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1313_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___f_1303_);
lean_ctor_set(v___x_1293_, 0, v___x_1311_);
v___x_1313_ = v___x_1293_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___f_1303_);
v___x_1313_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1314_; lean_object* v_toApplicative_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1347_; 
v___x_1314_ = l_StateRefT_x27_instMonad___redArg(v___x_1313_);
v_toApplicative_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1314_, 1);
lean_dec(v_unused_1348_);
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1347_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_toApplicative_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1347_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_toFunctor_1319_; lean_object* v_toSeq_1320_; lean_object* v_toSeqLeft_1321_; lean_object* v_toSeqRight_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1345_; 
v_toFunctor_1319_ = lean_ctor_get(v_toApplicative_1315_, 0);
v_toSeq_1320_ = lean_ctor_get(v_toApplicative_1315_, 2);
v_toSeqLeft_1321_ = lean_ctor_get(v_toApplicative_1315_, 3);
v_toSeqRight_1322_ = lean_ctor_get(v_toApplicative_1315_, 4);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_toApplicative_1315_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_toApplicative_1315_, 1);
lean_dec(v_unused_1346_);
v___x_1324_ = v_toApplicative_1315_;
v_isShared_1325_ = v_isSharedCheck_1345_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_toSeqRight_1322_);
lean_inc(v_toSeqLeft_1321_);
lean_inc(v_toSeq_1320_);
lean_inc(v_toFunctor_1319_);
lean_dec(v_toApplicative_1315_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1345_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1335_; 
v___f_1326_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1327_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1319_);
v___f_1328_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1328_, 0, v_toFunctor_1319_);
v___f_1329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1329_, 0, v_toFunctor_1319_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___f_1328_);
lean_ctor_set(v___x_1330_, 1, v___f_1329_);
v___f_1331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1331_, 0, v_toSeqRight_1322_);
v___f_1332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1332_, 0, v_toSeqLeft_1321_);
v___f_1333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1333_, 0, v_toSeq_1320_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 4, v___f_1331_);
lean_ctor_set(v___x_1324_, 3, v___f_1332_);
lean_ctor_set(v___x_1324_, 2, v___f_1333_);
lean_ctor_set(v___x_1324_, 1, v___f_1326_);
lean_ctor_set(v___x_1324_, 0, v___x_1330_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v___f_1326_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v___f_1333_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v___f_1332_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v___f_1331_);
v___x_1335_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___f_1327_);
lean_ctor_set(v___x_1317_, 0, v___x_1335_);
v___x_1337_ = v___x_1317_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v___f_1327_);
v___x_1337_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_4540__overap_1341_; lean_object* v___x_1342_; 
v___x_1338_ = l_StateRefT_x27_instMonad___redArg(v___x_1337_);
v___x_1339_ = lean_box(0);
v___x_1340_ = l_instInhabitedOfMonad___redArg(v___x_1338_, v___x_1339_);
v___x_4540__overap_1341_ = lean_panic_fn_borrowed(v___x_1340_, v_msg_1282_);
lean_dec(v___x_1340_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
v___x_1342_ = lean_apply_6(v___x_4540__overap_1341_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
return v___x_1342_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
return v_res_1362_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1364_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1365_ = lean_unsigned_to_nat(11u);
v___x_1366_ = lean_unsigned_to_nat(158u);
v___x_1367_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1368_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1369_ = l_mkPanicMessageWithDecl(v___x_1368_, v___x_1367_, v___x_1366_, v___x_1365_, v___x_1364_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1370_, lean_object* v_a_1371_, lean_object* v_b_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v_a_1380_; uint8_t v___x_1384_; 
v___x_1384_ = lean_nat_dec_lt(v_a_1371_, v_upperBound_1370_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; 
lean_dec(v_a_1371_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v_b_1372_);
return v___x_1385_;
}
else
{
if (lean_obj_tag(v_b_1372_) == 7)
{
lean_object* v_body_1386_; 
v_body_1386_ = lean_ctor_get(v_b_1372_, 2);
lean_inc_ref(v_body_1386_);
lean_dec_ref_known(v_b_1372_, 3);
v_a_1380_ = v_body_1386_;
goto v___jp_1379_;
}
else
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1388_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1387_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_dec_ref_known(v___x_1388_, 1);
v_a_1380_ = v_b_1372_;
goto v___jp_1379_;
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_b_1372_);
lean_dec(v_a_1371_);
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1388_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1388_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
v___jp_1379_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_nat_add(v_a_1371_, v___x_1381_);
lean_dec(v_a_1371_);
v_a_1371_ = v___x_1382_;
v_b_1372_ = v_a_1380_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1397_, lean_object* v_a_1398_, lean_object* v_b_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1397_, v_a_1398_, v_b_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec(v_upperBound_1397_);
return v_res_1406_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1407_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1408_ = lean_unsigned_to_nat(11u);
v___x_1409_ = lean_unsigned_to_nat(166u);
v___x_1410_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1411_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1412_ = l_mkPanicMessageWithDecl(v___x_1411_, v___x_1410_, v___x_1409_, v___x_1408_, v___x_1407_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1413_, lean_object* v_a_1414_, lean_object* v_b_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_a_1423_; uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_lt(v_a_1414_, v_upperBound_1413_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
lean_dec(v_a_1414_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1415_);
return v___x_1428_;
}
else
{
lean_object* v_fst_1429_; 
v_fst_1429_ = lean_ctor_get(v_b_1415_, 0);
lean_inc(v_fst_1429_);
if (lean_obj_tag(v_fst_1429_) == 7)
{
lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1463_; 
v_snd_1430_ = lean_ctor_get(v_b_1415_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_b_1415_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_b_1415_, 0);
lean_dec(v_unused_1464_);
v___x_1432_ = v_b_1415_;
v_isShared_1433_ = v_isSharedCheck_1463_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_dec(v_b_1415_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1463_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_binderName_1434_; lean_object* v_binderType_1435_; lean_object* v_body_1436_; lean_object* v___x_1437_; 
v_binderName_1434_ = lean_ctor_get(v_fst_1429_, 0);
lean_inc(v_binderName_1434_);
v_binderType_1435_ = lean_ctor_get(v_fst_1429_, 1);
lean_inc_ref(v_binderType_1435_);
v_body_1436_ = lean_ctor_get(v_fst_1429_, 2);
lean_inc_ref(v_body_1436_);
lean_dec_ref_known(v_fst_1429_, 3);
v___x_1437_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1435_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; uint8_t v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = 0;
v___x_1440_ = 0;
v___x_1441_ = l_Lean_Compiler_LCNF_mkParam(v___x_1439_, v_binderName_1434_, v_a_1438_, v___x_1440_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = lean_array_push(v_snd_1430_, v_a_1442_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___x_1443_);
lean_ctor_set(v___x_1432_, 0, v_body_1436_);
v___x_1445_ = v___x_1432_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_body_1436_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
v_a_1423_ = v___x_1445_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_body_1436_);
lean_del_object(v___x_1432_);
lean_dec(v_snd_1430_);
lean_dec(v_a_1414_);
v_a_1447_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1441_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1441_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v_body_1436_);
lean_dec(v_binderName_1434_);
lean_del_object(v___x_1432_);
lean_dec(v_snd_1430_);
lean_dec(v_a_1414_);
v_a_1455_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1437_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1437_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v_snd_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1482_; 
v_snd_1465_ = lean_ctor_get(v_b_1415_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_b_1415_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_b_1415_, 0);
lean_dec(v_unused_1483_);
v___x_1467_ = v_b_1415_;
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_snd_1465_);
lean_dec(v_b_1415_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1470_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1469_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1472_; 
lean_dec_ref_known(v___x_1470_, 1);
if (v_isShared_1468_ == 0)
{
v___x_1472_ = v___x_1467_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_fst_1429_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_snd_1465_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
v_a_1423_ = v___x_1472_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_del_object(v___x_1467_);
lean_dec(v_snd_1465_);
lean_dec(v_fst_1429_);
lean_dec(v_a_1414_);
v_a_1474_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1470_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_add(v_a_1414_, v___x_1424_);
lean_dec(v_a_1414_);
v_a_1414_ = v___x_1425_;
v_b_1415_ = v_a_1423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1484_, v_a_1485_, v_b_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec(v_upperBound_1484_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1494_, lean_object* v_numParams_1495_, lean_object* v_numNewFields_1496_, lean_object* v_oldFields_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1495_, v___x_1504_, v_ctorType_1494_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref_known(v___x_1505_, 1);
v___x_1507_ = lean_array_get_size(v_oldFields_1497_);
v___x_1508_ = lean_nat_add(v___x_1507_, v_numNewFields_1496_);
v___x_1509_ = lean_mk_empty_array_with_capacity(v___x_1508_);
lean_dec(v___x_1508_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1506_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1496_, v___x_1504_, v___x_1510_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1521_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1521_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1521_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_snd_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v_snd_1516_ = lean_ctor_get(v_a_1512_, 1);
lean_inc(v_snd_1516_);
lean_dec(v_a_1512_);
v___x_1517_ = l_Array_append___redArg(v_snd_1516_, v_oldFields_1497_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 0, v___x_1517_);
v___x_1519_ = v___x_1514_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_a_1522_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1511_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1511_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
v_a_1530_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1505_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1505_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1538_, lean_object* v_numParams_1539_, lean_object* v_numNewFields_1540_, lean_object* v_oldFields_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1538_, v_numParams_1539_, v_numNewFields_1540_, v_oldFields_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_oldFields_1541_);
lean_dec(v_numNewFields_1540_);
lean_dec(v_numParams_1539_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1549_, lean_object* v_inst_1550_, lean_object* v_R_1551_, lean_object* v_a_1552_, lean_object* v_b_1553_, lean_object* v_c_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1549_, v_a_1552_, v_b_1553_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1562_, lean_object* v_inst_1563_, lean_object* v_R_1564_, lean_object* v_a_1565_, lean_object* v_b_1566_, lean_object* v_c_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1562_, v_inst_1563_, v_R_1564_, v_a_1565_, v_b_1566_, v_c_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
lean_dec(v___y_1568_);
lean_dec(v_upperBound_1562_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1575_, lean_object* v_inst_1576_, lean_object* v_R_1577_, lean_object* v_a_1578_, lean_object* v_b_1579_, lean_object* v_c_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1575_, v_a_1578_, v_b_1579_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1588_, lean_object* v_inst_1589_, lean_object* v_R_1590_, lean_object* v_a_1591_, lean_object* v_b_1592_, lean_object* v_c_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1588_, v_inst_1589_, v_R_1590_, v_a_1591_, v_b_1592_, v_c_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec(v_upperBound_1588_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1601_, size_t v_i_1602_, lean_object* v_bs_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_1609_; 
v___x_1609_ = lean_usize_dec_lt(v_i_1602_, v_sz_1601_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1610_, 0, v_bs_1603_);
return v___x_1610_;
}
else
{
lean_object* v_v_1611_; lean_object* v___x_1612_; 
v_v_1611_ = lean_array_uget_borrowed(v_bs_1603_, v_i_1602_);
lean_inc(v_v_1611_);
v___x_1612_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1611_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v_bs_x27_1615_; size_t v___x_1616_; size_t v___x_1617_; lean_object* v___x_1618_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = lean_unsigned_to_nat(0u);
v_bs_x27_1615_ = lean_array_uset(v_bs_1603_, v_i_1602_, v___x_1614_);
v___x_1616_ = ((size_t)1ULL);
v___x_1617_ = lean_usize_add(v_i_1602_, v___x_1616_);
v___x_1618_ = lean_array_uset(v_bs_x27_1615_, v_i_1602_, v_a_1613_);
v_i_1602_ = v___x_1617_;
v_bs_1603_ = v___x_1618_;
goto _start;
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_bs_1603_);
v_a_1620_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1612_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1612_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1628_, lean_object* v_i_1629_, lean_object* v_bs_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
size_t v_sz_boxed_1636_; size_t v_i_boxed_1637_; lean_object* v_res_1638_; 
v_sz_boxed_1636_ = lean_unbox_usize(v_sz_1628_);
lean_dec(v_sz_1628_);
v_i_boxed_1637_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1636_, v_i_boxed_1637_, v_bs_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v___y_1631_);
return v_res_1638_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = 0;
v___x_1640_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_toApplicative_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1712_; 
v___x_1648_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1649_ = l_StateRefT_x27_instMonad___redArg(v___x_1648_);
v_toApplicative_1650_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v___x_1649_, 1);
lean_dec(v_unused_1713_);
v___x_1652_ = v___x_1649_;
v_isShared_1653_ = v_isSharedCheck_1712_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_toApplicative_1650_);
lean_dec(v___x_1649_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1712_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_toFunctor_1654_; lean_object* v_toSeq_1655_; lean_object* v_toSeqLeft_1656_; lean_object* v_toSeqRight_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1710_; 
v_toFunctor_1654_ = lean_ctor_get(v_toApplicative_1650_, 0);
v_toSeq_1655_ = lean_ctor_get(v_toApplicative_1650_, 2);
v_toSeqLeft_1656_ = lean_ctor_get(v_toApplicative_1650_, 3);
v_toSeqRight_1657_ = lean_ctor_get(v_toApplicative_1650_, 4);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_toApplicative_1650_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_toApplicative_1650_, 1);
lean_dec(v_unused_1711_);
v___x_1659_ = v_toApplicative_1650_;
v_isShared_1660_ = v_isSharedCheck_1710_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_toSeqRight_1657_);
lean_inc(v_toSeqLeft_1656_);
lean_inc(v_toSeq_1655_);
lean_inc(v_toFunctor_1654_);
lean_dec(v_toApplicative_1650_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1710_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___f_1661_; lean_object* v___f_1662_; lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; lean_object* v___f_1668_; lean_object* v___x_1670_; 
v___f_1661_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1662_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1654_);
v___f_1663_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1663_, 0, v_toFunctor_1654_);
v___f_1664_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1664_, 0, v_toFunctor_1654_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___f_1663_);
lean_ctor_set(v___x_1665_, 1, v___f_1664_);
v___f_1666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1666_, 0, v_toSeqRight_1657_);
v___f_1667_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1667_, 0, v_toSeqLeft_1656_);
v___f_1668_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1668_, 0, v_toSeq_1655_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v___f_1666_);
lean_ctor_set(v___x_1659_, 3, v___f_1667_);
lean_ctor_set(v___x_1659_, 2, v___f_1668_);
lean_ctor_set(v___x_1659_, 1, v___f_1661_);
lean_ctor_set(v___x_1659_, 0, v___x_1665_);
v___x_1670_ = v___x_1659_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___f_1661_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v___f_1668_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v___f_1667_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v___f_1666_);
v___x_1670_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v___f_1662_);
lean_ctor_set(v___x_1652_, 0, v___x_1670_);
v___x_1672_ = v___x_1652_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1670_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___f_1662_);
v___x_1672_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1673_; lean_object* v_toApplicative_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1706_; 
v___x_1673_ = l_StateRefT_x27_instMonad___redArg(v___x_1672_);
v_toApplicative_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v___x_1673_, 1);
lean_dec(v_unused_1707_);
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1706_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_toApplicative_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1706_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_toFunctor_1678_; lean_object* v_toSeq_1679_; lean_object* v_toSeqLeft_1680_; lean_object* v_toSeqRight_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1704_; 
v_toFunctor_1678_ = lean_ctor_get(v_toApplicative_1674_, 0);
v_toSeq_1679_ = lean_ctor_get(v_toApplicative_1674_, 2);
v_toSeqLeft_1680_ = lean_ctor_get(v_toApplicative_1674_, 3);
v_toSeqRight_1681_ = lean_ctor_get(v_toApplicative_1674_, 4);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_toApplicative_1674_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v_toApplicative_1674_, 1);
lean_dec(v_unused_1705_);
v___x_1683_ = v_toApplicative_1674_;
v_isShared_1684_ = v_isSharedCheck_1704_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_toSeqRight_1681_);
lean_inc(v_toSeqLeft_1680_);
lean_inc(v_toSeq_1679_);
lean_inc(v_toFunctor_1678_);
lean_dec(v_toApplicative_1674_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1704_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___x_1694_; 
v___f_1685_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1686_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1678_);
v___f_1687_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1687_, 0, v_toFunctor_1678_);
v___f_1688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1688_, 0, v_toFunctor_1678_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___f_1687_);
lean_ctor_set(v___x_1689_, 1, v___f_1688_);
v___f_1690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1690_, 0, v_toSeqRight_1681_);
v___f_1691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1691_, 0, v_toSeqLeft_1680_);
v___f_1692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1692_, 0, v_toSeq_1679_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 4, v___f_1690_);
lean_ctor_set(v___x_1683_, 3, v___f_1691_);
lean_ctor_set(v___x_1683_, 2, v___f_1692_);
lean_ctor_set(v___x_1683_, 1, v___f_1685_);
lean_ctor_set(v___x_1683_, 0, v___x_1689_);
v___x_1694_ = v___x_1683_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___f_1685_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v___f_1692_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v___f_1691_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v___f_1690_);
v___x_1694_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___f_1686_);
lean_ctor_set(v___x_1676_, 0, v___x_1694_);
v___x_1696_ = v___x_1676_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___f_1686_);
v___x_1696_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_43620__overap_1700_; lean_object* v___x_1701_; 
v___x_1697_ = l_StateRefT_x27_instMonad___redArg(v___x_1696_);
v___x_1698_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1699_ = l_instInhabitedOfMonad___redArg(v___x_1697_, v___x_1698_);
v___x_43620__overap_1700_ = lean_panic_fn_borrowed(v___x_1699_, v_msg_1641_);
lean_dec(v___x_1699_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v___y_1644_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1642_);
v___x_1701_ = lean_apply_6(v___x_43620__overap_1700_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, lean_box(0));
return v___x_1701_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1724_ = lean_panic_fn_borrowed(v___x_1723_, v_msg_1722_);
return v___x_1724_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
uint8_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = 0;
v___x_1726_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_toApplicative_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1798_; 
v___x_1734_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1735_ = l_StateRefT_x27_instMonad___redArg(v___x_1734_);
v_toApplicative_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v___x_1735_, 1);
lean_dec(v_unused_1799_);
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1798_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_toApplicative_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1798_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_toFunctor_1740_; lean_object* v_toSeq_1741_; lean_object* v_toSeqLeft_1742_; lean_object* v_toSeqRight_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1796_; 
v_toFunctor_1740_ = lean_ctor_get(v_toApplicative_1736_, 0);
v_toSeq_1741_ = lean_ctor_get(v_toApplicative_1736_, 2);
v_toSeqLeft_1742_ = lean_ctor_get(v_toApplicative_1736_, 3);
v_toSeqRight_1743_ = lean_ctor_get(v_toApplicative_1736_, 4);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_toApplicative_1736_);
if (v_isSharedCheck_1796_ == 0)
{
lean_object* v_unused_1797_; 
v_unused_1797_ = lean_ctor_get(v_toApplicative_1736_, 1);
lean_dec(v_unused_1797_);
v___x_1745_ = v_toApplicative_1736_;
v_isShared_1746_ = v_isSharedCheck_1796_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_toSeqRight_1743_);
lean_inc(v_toSeqLeft_1742_);
lean_inc(v_toSeq_1741_);
lean_inc(v_toFunctor_1740_);
lean_dec(v_toApplicative_1736_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1796_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___f_1747_; lean_object* v___f_1748_; lean_object* v___f_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___f_1753_; lean_object* v___f_1754_; lean_object* v___x_1756_; 
v___f_1747_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1748_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1740_);
v___f_1749_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1749_, 0, v_toFunctor_1740_);
v___f_1750_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1750_, 0, v_toFunctor_1740_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___f_1749_);
lean_ctor_set(v___x_1751_, 1, v___f_1750_);
v___f_1752_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1752_, 0, v_toSeqRight_1743_);
v___f_1753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1753_, 0, v_toSeqLeft_1742_);
v___f_1754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1754_, 0, v_toSeq_1741_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 4, v___f_1752_);
lean_ctor_set(v___x_1745_, 3, v___f_1753_);
lean_ctor_set(v___x_1745_, 2, v___f_1754_);
lean_ctor_set(v___x_1745_, 1, v___f_1747_);
lean_ctor_set(v___x_1745_, 0, v___x_1751_);
v___x_1756_ = v___x_1745_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1751_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___f_1747_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v___f_1754_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v___f_1753_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v___f_1752_);
v___x_1756_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v___f_1748_);
lean_ctor_set(v___x_1738_, 0, v___x_1756_);
v___x_1758_ = v___x_1738_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___f_1748_);
v___x_1758_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1759_; lean_object* v_toApplicative_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1792_; 
v___x_1759_ = l_StateRefT_x27_instMonad___redArg(v___x_1758_);
v_toApplicative_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1792_ == 0)
{
lean_object* v_unused_1793_; 
v_unused_1793_ = lean_ctor_get(v___x_1759_, 1);
lean_dec(v_unused_1793_);
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1792_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_toApplicative_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1792_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_toFunctor_1764_; lean_object* v_toSeq_1765_; lean_object* v_toSeqLeft_1766_; lean_object* v_toSeqRight_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1790_; 
v_toFunctor_1764_ = lean_ctor_get(v_toApplicative_1760_, 0);
v_toSeq_1765_ = lean_ctor_get(v_toApplicative_1760_, 2);
v_toSeqLeft_1766_ = lean_ctor_get(v_toApplicative_1760_, 3);
v_toSeqRight_1767_ = lean_ctor_get(v_toApplicative_1760_, 4);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_toApplicative_1760_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_toApplicative_1760_, 1);
lean_dec(v_unused_1791_);
v___x_1769_ = v_toApplicative_1760_;
v_isShared_1770_ = v_isSharedCheck_1790_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_toSeqRight_1767_);
lean_inc(v_toSeqLeft_1766_);
lean_inc(v_toSeq_1765_);
lean_inc(v_toFunctor_1764_);
lean_dec(v_toApplicative_1760_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1790_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___f_1771_; lean_object* v___f_1772_; lean_object* v___f_1773_; lean_object* v___f_1774_; lean_object* v___x_1775_; lean_object* v___f_1776_; lean_object* v___f_1777_; lean_object* v___f_1778_; lean_object* v___x_1780_; 
v___f_1771_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1772_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1764_);
v___f_1773_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1773_, 0, v_toFunctor_1764_);
v___f_1774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1774_, 0, v_toFunctor_1764_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___f_1773_);
lean_ctor_set(v___x_1775_, 1, v___f_1774_);
v___f_1776_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1776_, 0, v_toSeqRight_1767_);
v___f_1777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1777_, 0, v_toSeqLeft_1766_);
v___f_1778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1778_, 0, v_toSeq_1765_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 4, v___f_1776_);
lean_ctor_set(v___x_1769_, 3, v___f_1777_);
lean_ctor_set(v___x_1769_, 2, v___f_1778_);
lean_ctor_set(v___x_1769_, 1, v___f_1771_);
lean_ctor_set(v___x_1769_, 0, v___x_1775_);
v___x_1780_ = v___x_1769_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v___f_1771_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v___f_1778_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v___f_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v___f_1776_);
v___x_1780_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___f_1772_);
lean_ctor_set(v___x_1762_, 0, v___x_1780_);
v___x_1782_ = v___x_1762_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___f_1772_);
v___x_1782_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_43635__overap_1786_; lean_object* v___x_1787_; 
v___x_1783_ = l_StateRefT_x27_instMonad___redArg(v___x_1782_);
v___x_1784_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1785_ = l_instInhabitedOfMonad___redArg(v___x_1783_, v___x_1784_);
v___x_43635__overap_1786_ = lean_panic_fn_borrowed(v___x_1785_, v_msg_1727_);
lean_dec(v___x_1785_);
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc(v___y_1730_);
lean_inc_ref(v___y_1729_);
lean_inc(v___y_1728_);
v___x_1787_ = lean_apply_6(v___x_43635__overap_1786_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, lean_box(0));
return v___x_1787_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
return v_res_1807_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1812_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1813_ = lean_unsigned_to_nat(66u);
v___x_1814_ = lean_unsigned_to_nat(411u);
v___x_1815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1816_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1817_ = l_mkPanicMessageWithDecl(v___x_1816_, v___x_1815_, v___x_1814_, v___x_1813_, v___x_1812_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_params_1825_; lean_object* v_type_1826_; lean_object* v_value_1827_; lean_object* v___x_1828_; 
v_params_1825_ = lean_ctor_get(v_decl_1818_, 2);
v_type_1826_ = lean_ctor_get(v_decl_1818_, 3);
v_value_1827_ = lean_ctor_get(v_decl_1818_, 4);
lean_inc_ref(v_type_1826_);
v___x_1828_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1826_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; size_t v_sz_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v_sz_1830_ = lean_array_size(v_params_1825_);
v___x_1831_ = ((size_t)0ULL);
lean_inc_ref(v_params_1825_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1830_, v___x_1831_, v_params_1825_, v_a_1819_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
lean_inc_ref(v_value_1827_);
v___x_1834_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_1827_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v___x_1836_ = 0;
v___x_1837_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_1836_, v_decl_1818_, v_a_1829_, v_a_1833_, v_a_1835_, v_a_1821_);
return v___x_1837_;
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1833_);
lean_dec(v_a_1829_);
lean_dec_ref(v_decl_1818_);
v_a_1838_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1834_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1834_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_a_1829_);
lean_dec_ref(v_decl_1818_);
v_a_1846_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1832_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1832_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
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
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_decl_1818_);
v_a_1854_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1828_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1828_);
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
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1865_ = lean_unsigned_to_nat(9u);
v___x_1866_ = lean_unsigned_to_nat(641u);
v___x_1867_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1868_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__2));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1870_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1871_ = lean_unsigned_to_nat(27u);
v___x_1872_ = lean_unsigned_to_nat(365u);
v___x_1873_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1874_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1875_ = l_mkPanicMessageWithDecl(v___x_1874_, v___x_1873_, v___x_1872_, v___x_1871_, v___x_1870_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1932_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1933_ = lean_unsigned_to_nat(2u);
v___x_1934_ = lean_unsigned_to_nat(348u);
v___x_1935_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1936_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1937_ = l_mkPanicMessageWithDecl(v___x_1936_, v___x_1935_, v___x_1934_, v___x_1933_, v___x_1932_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1939_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1940_ = lean_unsigned_to_nat(2u);
v___x_1941_ = lean_unsigned_to_nat(350u);
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1943_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1944_ = l_mkPanicMessageWithDecl(v___x_1943_, v___x_1942_, v___x_1941_, v___x_1940_, v___x_1939_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1946_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1947_ = lean_unsigned_to_nat(2u);
v___x_1948_ = lean_unsigned_to_nat(351u);
v___x_1949_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1950_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1951_ = l_mkPanicMessageWithDecl(v___x_1950_, v___x_1949_, v___x_1948_, v___x_1947_, v___x_1946_);
return v___x_1951_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1952_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1953_ = lean_unsigned_to_nat(41u);
v___x_1954_ = lean_unsigned_to_nat(349u);
v___x_1955_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1956_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_1957_ = l_mkPanicMessageWithDecl(v___x_1956_, v___x_1955_, v___x_1954_, v___x_1953_, v___x_1952_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1958_, lean_object* v_c_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_discr_1966_; lean_object* v_alts_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2045_; 
v_discr_1966_ = lean_ctor_get(v_c_1959_, 2);
v_alts_1967_ = lean_ctor_get(v_c_1959_, 3);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_c_1959_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; lean_object* v_unused_2047_; 
v_unused_2046_ = lean_ctor_get(v_c_1959_, 1);
lean_dec(v_unused_2046_);
v_unused_2047_ = lean_ctor_get(v_c_1959_, 0);
lean_dec(v_unused_2047_);
v___x_1969_ = v_c_1959_;
v_isShared_1970_ = v_isSharedCheck_2045_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_alts_1967_);
lean_inc(v_discr_1966_);
lean_dec(v_c_1959_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2045_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1971_ = lean_array_get_size(v_alts_1967_);
v___x_1972_ = lean_unsigned_to_nat(1u);
v___x_1973_ = lean_nat_dec_eq(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1969_);
lean_dec_ref(v_alts_1967_);
lean_dec(v_discr_1966_);
v___x_1974_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1975_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1974_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
return v___x_1975_;
}
else
{
uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1976_ = 0;
v___x_1977_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = lean_array_get(v___x_1977_, v_alts_1967_, v___x_1978_);
lean_dec_ref(v_alts_1967_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_ctorName_1980_; lean_object* v_params_1981_; lean_object* v_code_1982_; lean_object* v_ctorName_1983_; lean_object* v_fieldIdx_1984_; uint8_t v___x_1985_; 
v_ctorName_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_ctorName_1980_);
v_params_1981_ = lean_ctor_get(v___x_1979_, 1);
lean_inc_ref(v_params_1981_);
v_code_1982_ = lean_ctor_get(v___x_1979_, 2);
lean_inc_ref(v_code_1982_);
lean_dec_ref_known(v___x_1979_, 3);
v_ctorName_1983_ = lean_ctor_get(v_info_1958_, 0);
v_fieldIdx_1984_ = lean_ctor_get(v_info_1958_, 2);
v___x_1985_ = lean_name_eq(v_ctorName_1980_, v_ctorName_1983_);
lean_dec(v_ctorName_1980_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec_ref(v_code_1982_);
lean_dec_ref(v_params_1981_);
lean_del_object(v___x_1969_);
lean_dec(v_discr_1966_);
v___x_1986_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1987_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1986_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = lean_array_get_size(v_params_1981_);
v___x_1989_ = lean_nat_dec_lt(v_fieldIdx_1984_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_code_1982_);
lean_dec_ref(v_params_1981_);
lean_del_object(v___x_1969_);
lean_dec(v_discr_1966_);
v___x_1990_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1991_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1990_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_1993_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1976_, v_params_1981_, v_a_1962_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_p_1994_; lean_object* v_fvarId_1995_; lean_object* v_binderName_1996_; lean_object* v_type_1997_; lean_object* v___x_1998_; 
lean_dec_ref_known(v___x_1993_, 1);
v_p_1994_ = lean_array_get(v___x_1992_, v_params_1981_, v_fieldIdx_1984_);
lean_dec_ref(v_params_1981_);
v_fvarId_1995_ = lean_ctor_get(v_p_1994_, 0);
lean_inc(v_fvarId_1995_);
v_binderName_1996_ = lean_ctor_get(v_p_1994_, 1);
lean_inc(v_binderName_1996_);
v_type_1997_ = lean_ctor_get(v_p_1994_, 2);
lean_inc_ref(v_type_1997_);
lean_dec(v_p_1994_);
v___x_1998_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1997_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; lean_object* v_lctx_2001_; lean_object* v_nextIdx_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2026_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2000_ = lean_st_ref_take(v_a_1962_);
v_lctx_2001_ = lean_ctor_get(v___x_2000_, 0);
v_nextIdx_2002_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2026_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_nextIdx_2002_);
lean_inc(v_lctx_2001_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2026_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2006_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_2007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_discr_1966_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 3, v___x_2007_);
lean_ctor_set(v___x_1969_, 2, v_a_1999_);
lean_ctor_set(v___x_1969_, 1, v_binderName_1996_);
lean_ctor_set(v___x_1969_, 0, v_fvarId_1995_);
v___x_2009_ = v___x_1969_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_fvarId_1995_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_binderName_1996_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_a_1999_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_inc_ref(v___x_2009_);
v___x_2010_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1976_, v_lctx_2001_, v___x_2009_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2010_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_nextIdx_2002_);
v___x_2012_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = lean_st_ref_set(v_a_1962_, v___x_2012_);
v___x_2014_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1982_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2009_);
lean_ctor_set(v___x_2019_, 1, v_a_2015_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2019_);
v___x_2021_ = v___x_2017_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
else
{
lean_dec_ref(v___x_2009_);
return v___x_2014_;
}
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_binderName_1996_);
lean_dec(v_fvarId_1995_);
lean_dec_ref(v_code_1982_);
lean_del_object(v___x_1969_);
lean_dec(v_discr_1966_);
v_a_2027_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1998_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1998_);
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
lean_dec_ref(v_code_1982_);
lean_dec_ref(v_params_1981_);
lean_del_object(v___x_1969_);
lean_dec(v_discr_1966_);
v_a_2035_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1993_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1993_);
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
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec(v___x_1979_);
lean_del_object(v___x_1969_);
lean_dec(v_discr_1966_);
v___x_2043_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_2044_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2043_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
return v___x_2044_;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_2050_ = lean_unsigned_to_nat(70u);
v___x_2051_ = lean_unsigned_to_nat(421u);
v___x_2052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_2053_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2054_ = l_mkPanicMessageWithDecl(v___x_2053_, v___x_2052_, v___x_2051_, v___x_2050_, v___x_2049_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_2058_, uint8_t v___x_2059_, size_t v_sz_2060_, size_t v_i_2061_, lean_object* v_bs_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_usize_dec_lt(v_i_2061_, v_sz_2060_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref(v___x_2058_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v_bs_2062_);
return v___x_2070_;
}
else
{
lean_object* v_v_2071_; lean_object* v___x_2072_; lean_object* v_bs_x27_2073_; lean_object* v_a_2075_; lean_object* v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; 
v_v_2071_ = lean_array_uget(v_bs_2062_, v_i_2061_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v_bs_x27_2073_ = lean_array_uset(v_bs_2062_, v_i_2061_, v___x_2072_);
if (lean_obj_tag(v_v_2071_) == 0)
{
lean_object* v_ctorName_2097_; lean_object* v_params_2098_; lean_object* v_code_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2137_; 
v_ctorName_2097_ = lean_ctor_get(v_v_2071_, 0);
v_params_2098_ = lean_ctor_get(v_v_2071_, 1);
v_code_2099_ = lean_ctor_get(v_v_2071_, 2);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_v_2071_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2101_ = v_v_2071_;
v_isShared_2102_ = v_isSharedCheck_2137_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_code_2099_);
lean_inc(v_params_2098_);
lean_inc(v_ctorName_2097_);
lean_dec(v_v_2071_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2137_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_2104_ = l_Lean_Name_append(v_ctorName_2097_, v___x_2103_);
lean_inc(v___x_2104_);
lean_inc_ref(v___x_2058_);
v___x_2105_ = l_Lean_Environment_find_x3f(v___x_2058_, v___x_2104_, v___x_2059_);
if (lean_obj_tag(v___x_2105_) == 1)
{
lean_object* v_val_2106_; 
v_val_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_val_2106_);
lean_dec_ref_known(v___x_2105_, 1);
if (lean_obj_tag(v_val_2106_) == 6)
{
lean_object* v_val_2107_; lean_object* v_toConstantVal_2108_; lean_object* v_numParams_2109_; lean_object* v_numFields_2110_; lean_object* v_type_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_val_2107_ = lean_ctor_get(v_val_2106_, 0);
lean_inc_ref(v_val_2107_);
lean_dec_ref_known(v_val_2106_, 1);
v_toConstantVal_2108_ = lean_ctor_get(v_val_2107_, 0);
lean_inc_ref(v_toConstantVal_2108_);
v_numParams_2109_ = lean_ctor_get(v_val_2107_, 3);
lean_inc(v_numParams_2109_);
v_numFields_2110_ = lean_ctor_get(v_val_2107_, 4);
lean_inc(v_numFields_2110_);
lean_dec_ref(v_val_2107_);
v_type_2111_ = lean_ctor_get(v_toConstantVal_2108_, 2);
lean_inc_ref(v_type_2111_);
lean_dec_ref(v_toConstantVal_2108_);
v___x_2112_ = lean_array_get_size(v_params_2098_);
v___x_2113_ = lean_nat_sub(v_numFields_2110_, v___x_2112_);
lean_dec(v_numFields_2110_);
v___x_2114_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_2111_, v_numParams_2109_, v___x_2113_, v_params_2098_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec_ref(v_params_2098_);
lean_dec(v___x_2113_);
lean_dec(v_numParams_2109_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2099_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 2, v_a_2117_);
lean_ctor_set(v___x_2101_, 1, v_a_2115_);
lean_ctor_set(v___x_2101_, 0, v___x_2104_);
v___x_2119_ = v___x_2101_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_a_2115_);
lean_ctor_set(v_reuseFailAlloc_2120_, 2, v_a_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
v_a_2075_ = v___x_2119_;
goto v___jp_2074_;
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_a_2115_);
lean_dec(v___x_2104_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_bs_x27_2073_);
lean_dec_ref(v___x_2058_);
v_a_2121_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2116_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2116_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v___x_2104_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_code_2099_);
lean_dec_ref(v_bs_x27_2073_);
lean_dec_ref(v___x_2058_);
v_a_2129_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2114_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2114_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_dec(v_val_2106_);
lean_dec(v___x_2104_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_code_2099_);
lean_dec_ref(v_params_2098_);
v___y_2081_ = v___y_2063_;
v___y_2082_ = v___y_2064_;
v___y_2083_ = v___y_2065_;
v___y_2084_ = v___y_2066_;
v___y_2085_ = v___y_2067_;
goto v___jp_2080_;
}
}
else
{
lean_dec(v___x_2105_);
lean_dec(v___x_2104_);
lean_del_object(v___x_2101_);
lean_dec_ref(v_code_2099_);
lean_dec_ref(v_params_2098_);
v___y_2081_ = v___y_2063_;
v___y_2082_ = v___y_2064_;
v___y_2083_ = v___y_2065_;
v___y_2084_ = v___y_2066_;
v___y_2085_ = v___y_2067_;
goto v___jp_2080_;
}
}
}
else
{
lean_object* v_code_2138_; lean_object* v___x_2139_; 
v_code_2138_ = lean_ctor_get(v_v_2071_, 0);
lean_inc_ref(v_code_2138_);
v___x_2139_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2138_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2071_, v_a_2140_);
v_a_2075_ = v___x_2141_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref_known(v_v_2071_, 1);
lean_dec_ref(v_bs_x27_2073_);
lean_dec_ref(v___x_2058_);
v_a_2142_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2139_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2139_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
v___jp_2074_:
{
size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_add(v_i_2061_, v___x_2076_);
v___x_2078_ = lean_array_uset(v_bs_x27_2073_, v_i_2061_, v_a_2075_);
v_i_2061_ = v___x_2077_;
v_bs_2062_ = v___x_2078_;
goto _start;
}
v___jp_2080_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_2087_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_2086_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v_a_2075_ = v_a_2088_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_bs_x27_2073_);
lean_dec_ref(v___x_2058_);
v_a_2089_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2087_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_2150_, size_t v_i_2151_, lean_object* v_bs_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v___x_2159_; 
v___x_2159_ = lean_usize_dec_lt(v_i_2151_, v_sz_2150_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2160_, 0, v_bs_2152_);
return v___x_2160_;
}
else
{
lean_object* v_v_2161_; lean_object* v___x_2162_; lean_object* v_bs_x27_2163_; lean_object* v_a_2165_; 
v_v_2161_ = lean_array_uget(v_bs_2152_, v_i_2151_);
v___x_2162_ = lean_unsigned_to_nat(0u);
v_bs_x27_2163_ = lean_array_uset(v_bs_2152_, v_i_2151_, v___x_2162_);
if (lean_obj_tag(v_v_2161_) == 0)
{
lean_object* v_params_2170_; lean_object* v_code_2171_; size_t v_sz_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v_params_2170_ = lean_ctor_get(v_v_2161_, 1);
v_code_2171_ = lean_ctor_get(v_v_2161_, 2);
v_sz_2172_ = lean_array_size(v_params_2170_);
v___x_2173_ = ((size_t)0ULL);
lean_inc_ref(v_params_2170_);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2172_, v___x_2173_, v_params_2170_, v___y_2153_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
lean_inc_ref(v_code_2171_);
v___x_2176_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2171_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; uint8_t v___x_2178_; lean_object* v___x_2179_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v___x_2178_ = 0;
v___x_2179_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_2178_, v_v_2161_, v_a_2175_, v_a_2177_);
v_a_2165_ = v___x_2179_;
goto v___jp_2164_;
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2175_);
lean_dec_ref_known(v_v_2161_, 3);
lean_dec_ref(v_bs_x27_2163_);
v_a_2180_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2176_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2176_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_2161_, 3);
lean_dec_ref(v_bs_x27_2163_);
return v___x_2174_;
}
}
else
{
lean_object* v_code_2188_; lean_object* v___x_2189_; 
v_code_2188_ = lean_ctor_get(v_v_2161_, 0);
lean_inc_ref(v_code_2188_);
v___x_2189_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2188_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; lean_object* v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v___x_2191_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2161_, v_a_2190_);
v_a_2165_ = v___x_2191_;
goto v___jp_2164_;
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref_known(v_v_2161_, 1);
lean_dec_ref(v_bs_x27_2163_);
v_a_2192_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2189_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2189_);
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
v___jp_2164_:
{
size_t v___x_2166_; size_t v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = ((size_t)1ULL);
v___x_2167_ = lean_usize_add(v_i_2151_, v___x_2166_);
v___x_2168_ = lean_array_uset(v_bs_x27_2163_, v_i_2151_, v_a_2165_);
v_i_2151_ = v___x_2167_;
v_bs_2152_ = v___x_2168_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2201_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2202_ = lean_unsigned_to_nat(2u);
v___x_2203_ = lean_unsigned_to_nat(337u);
v___x_2204_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2205_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2206_ = l_mkPanicMessageWithDecl(v___x_2205_, v___x_2204_, v___x_2203_, v___x_2202_, v___x_2201_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_unsigned_to_nat(2u);
v___x_2213_ = lean_mk_empty_array_with_capacity(v___x_2212_);
v___x_2214_ = lean_array_push(v___x_2213_, v___x_2211_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2215_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2216_ = lean_unsigned_to_nat(34u);
v___x_2217_ = lean_unsigned_to_nat(338u);
v___x_2218_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2219_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2220_ = l_mkPanicMessageWithDecl(v___x_2219_, v___x_2218_, v___x_2217_, v___x_2216_, v___x_2215_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_discr_2228_; lean_object* v_alts_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2298_; 
v_discr_2228_ = lean_ctor_get(v_c_2221_, 2);
v_alts_2229_ = lean_ctor_get(v_c_2221_, 3);
v_isSharedCheck_2298_ = !lean_is_exclusive(v_c_2221_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; lean_object* v_unused_2300_; 
v_unused_2299_ = lean_ctor_get(v_c_2221_, 1);
lean_dec(v_unused_2299_);
v_unused_2300_ = lean_ctor_get(v_c_2221_, 0);
lean_dec(v_unused_2300_);
v___x_2231_ = v_c_2221_;
v_isShared_2232_ = v_isSharedCheck_2298_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_alts_2229_);
lean_inc(v_discr_2228_);
lean_dec(v_c_2221_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2298_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2233_ = lean_array_get_size(v_alts_2229_);
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_dec_eq(v___x_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_del_object(v___x_2231_);
lean_dec_ref(v_alts_2229_);
lean_dec(v_discr_2228_);
v___x_2236_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_2237_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2236_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v___x_2237_;
}
else
{
uint8_t v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2238_ = 0;
v___x_2239_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = lean_array_get(v___x_2239_, v_alts_2229_, v___x_2240_);
lean_dec_ref(v_alts_2229_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_params_2242_; lean_object* v_code_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2294_; 
v_params_2242_ = lean_ctor_get(v___x_2241_, 1);
v_code_2243_ = lean_ctor_get(v___x_2241_, 2);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; 
v_unused_2295_ = lean_ctor_get(v___x_2241_, 0);
lean_dec(v_unused_2295_);
v___x_2245_ = v___x_2241_;
v_isShared_2246_ = v_isSharedCheck_2294_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_code_2243_);
lean_inc(v_params_2242_);
lean_dec(v___x_2241_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2294_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2238_, v_params_2242_, v_a_2224_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_fvarId_2251_; lean_object* v_binderName_2252_; lean_object* v_lctx_2253_; lean_object* v_nextIdx_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref_known(v___x_2247_, 1);
v___x_2248_ = lean_st_ref_take(v_a_2224_);
v___x_2249_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2250_ = lean_array_get(v___x_2249_, v_params_2242_, v___x_2240_);
lean_dec_ref(v_params_2242_);
v_fvarId_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_fvarId_2251_);
v_binderName_2252_ = lean_ctor_get(v___x_2250_, 1);
lean_inc(v_binderName_2252_);
lean_dec(v___x_2250_);
v_lctx_2253_ = lean_ctor_get(v___x_2248_, 0);
v_nextIdx_2254_ = lean_ctor_get(v___x_2248_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2256_ = v___x_2248_;
v_isShared_2257_ = v_isSharedCheck_2285_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_nextIdx_2254_);
lean_inc(v_lctx_2253_);
lean_dec(v___x_2248_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2285_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2258_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_2259_ = lean_box(0);
v___x_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_discr_2228_);
v___x_2261_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2262_ = lean_array_push(v___x_2261_, v___x_2260_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 3);
lean_ctor_set(v___x_2245_, 2, v___x_2262_);
lean_ctor_set(v___x_2245_, 1, v___x_2259_);
lean_ctor_set(v___x_2245_, 0, v___x_2258_);
v___x_2264_ = v___x_2245_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2284_, 2, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2265_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 3, v___x_2264_);
lean_ctor_set(v___x_2231_, 2, v___x_2265_);
lean_ctor_set(v___x_2231_, 1, v_binderName_2252_);
lean_ctor_set(v___x_2231_, 0, v_fvarId_2251_);
v___x_2267_ = v___x_2231_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_fvarId_2251_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_binderName_2252_);
lean_ctor_set(v_reuseFailAlloc_2283_, 2, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2283_, 3, v___x_2264_);
v___x_2267_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
lean_inc_ref(v___x_2267_);
v___x_2268_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2238_, v_lctx_2253_, v___x_2267_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2268_);
v___x_2270_ = v___x_2256_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_nextIdx_2254_);
v___x_2270_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_st_ref_set(v_a_2224_, v___x_2270_);
v___x_2272_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2243_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2267_);
lean_ctor_set(v___x_2277_, 1, v_a_2273_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
else
{
lean_dec_ref(v___x_2267_);
return v___x_2272_;
}
}
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_del_object(v___x_2245_);
lean_dec_ref(v_code_2243_);
lean_dec_ref(v_params_2242_);
lean_del_object(v___x_2231_);
lean_dec(v_discr_2228_);
v_a_2286_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2247_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2247_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec(v___x_2241_);
lean_del_object(v___x_2231_);
lean_dec(v_discr_2228_);
v___x_2296_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_2297_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2296_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
return v___x_2297_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2302_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2303_ = lean_unsigned_to_nat(2u);
v___x_2304_ = lean_unsigned_to_nat(317u);
v___x_2305_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2306_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2307_ = l_mkPanicMessageWithDecl(v___x_2306_, v___x_2305_, v___x_2304_, v___x_2303_, v___x_2302_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_box(0);
v___x_2315_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_2316_ = l_Lean_Expr_const___override(v___x_2315_, v___x_2314_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2318_ = lean_unsigned_to_nat(34u);
v___x_2319_ = lean_unsigned_to_nat(318u);
v___x_2320_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2321_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2322_ = l_mkPanicMessageWithDecl(v___x_2321_, v___x_2320_, v___x_2319_, v___x_2318_, v___x_2317_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_discr_2330_; lean_object* v_alts_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v_discr_2330_ = lean_ctor_get(v_c_2323_, 2);
v_alts_2331_ = lean_ctor_get(v_c_2323_, 3);
v___x_2332_ = lean_array_get_size(v_alts_2331_);
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_dec_eq(v___x_2332_, v___x_2333_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_2336_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2335_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2336_;
}
else
{
uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2337_ = 0;
v___x_2338_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2339_ = lean_unsigned_to_nat(0u);
v___x_2340_ = lean_array_get(v___x_2338_, v_alts_2331_, v___x_2339_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_params_2341_; lean_object* v_code_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2439_; 
v_params_2341_ = lean_ctor_get(v___x_2340_, 1);
v_code_2342_ = lean_ctor_get(v___x_2340_, 2);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v___x_2340_, 0);
lean_dec(v_unused_2440_);
v___x_2344_ = v___x_2340_;
v_isShared_2345_ = v_isSharedCheck_2439_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_code_2342_);
lean_inc(v_params_2341_);
lean_dec(v___x_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2439_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2337_, v_params_2341_, v_a_2326_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref_known(v___x_2346_, 1);
v___x_2347_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2348_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2347_, v_a_2326_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
lean_inc(v_discr_2330_);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v_discr_2330_);
v___x_2352_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2353_ = lean_box(0);
v___x_2354_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2355_ = lean_array_push(v___x_2354_, v___x_2351_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set_tag(v___x_2344_, 3);
lean_ctor_set(v___x_2344_, 2, v___x_2355_);
lean_ctor_set(v___x_2344_, 1, v___x_2353_);
lean_ctor_set(v___x_2344_, 0, v___x_2352_);
v___x_2357_ = v___x_2344_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2359_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2337_, v_a_2349_, v___x_2358_, v___x_2357_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2362_ = 0;
v___x_2363_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_2337_, v___x_2361_, v___x_2362_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = l_Lean_mkArrow(v___x_2361_, v___x_2358_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v_fvarId_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v_fvarId_2370_; lean_object* v_binderName_2371_; lean_object* v_lctx_2372_; lean_object* v_nextIdx_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2397_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v_fvarId_2367_ = lean_ctor_get(v_a_2360_, 0);
v___x_2368_ = lean_st_ref_take(v_a_2326_);
v___x_2369_ = lean_array_get(v___x_2350_, v_params_2341_, v___x_2339_);
lean_dec_ref(v_params_2341_);
v_fvarId_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_fvarId_2370_);
v_binderName_2371_ = lean_ctor_get(v___x_2369_, 1);
lean_inc(v_binderName_2371_);
lean_dec(v___x_2369_);
v_lctx_2372_ = lean_ctor_get(v___x_2368_, 0);
v_nextIdx_2373_ = lean_ctor_get(v___x_2368_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2375_ = v___x_2368_;
v_isShared_2376_ = v_isSharedCheck_2397_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_nextIdx_2373_);
lean_inc(v_lctx_2372_);
lean_dec(v___x_2368_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2397_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_inc(v_fvarId_2367_);
v___x_2377_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_fvarId_2367_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2360_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_mk_empty_array_with_capacity(v___x_2333_);
v___x_2380_ = lean_array_push(v___x_2379_, v_a_2364_);
v___x_2381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2381_, 0, v_fvarId_2370_);
lean_ctor_set(v___x_2381_, 1, v_binderName_2371_);
lean_ctor_set(v___x_2381_, 2, v___x_2380_);
lean_ctor_set(v___x_2381_, 3, v_a_2366_);
lean_ctor_set(v___x_2381_, 4, v___x_2378_);
lean_inc_ref(v___x_2381_);
v___x_2382_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2337_, v_lctx_2372_, v___x_2381_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 0, v___x_2382_);
v___x_2384_ = v___x_2375_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_nextIdx_2373_);
v___x_2384_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_st_ref_set(v_a_2326_, v___x_2384_);
v___x_2386_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2342_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2395_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2395_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2381_);
lean_ctor_set(v___x_2391_, 1, v_a_2387_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2391_);
v___x_2393_ = v___x_2389_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
else
{
lean_dec_ref_known(v___x_2381_, 5);
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v_a_2364_);
lean_dec(v_a_2360_);
lean_dec_ref(v_code_2342_);
lean_dec_ref(v_params_2341_);
v_a_2398_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2365_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2365_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec(v_a_2360_);
lean_dec_ref(v_code_2342_);
lean_dec_ref(v_params_2341_);
v_a_2406_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2363_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2363_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_code_2342_);
lean_dec_ref(v_params_2341_);
v_a_2414_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2359_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2359_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_del_object(v___x_2344_);
lean_dec_ref(v_code_2342_);
lean_dec_ref(v_params_2341_);
v_a_2423_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2348_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2348_);
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
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_del_object(v___x_2344_);
lean_dec_ref(v_code_2342_);
lean_dec_ref(v_params_2341_);
v_a_2431_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2346_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2346_);
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
lean_dec(v___x_2340_);
v___x_2441_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2442_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2441_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2442_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2444_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2445_ = lean_unsigned_to_nat(2u);
v___x_2446_ = lean_unsigned_to_nat(306u);
v___x_2447_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2448_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2449_ = l_mkPanicMessageWithDecl(v___x_2448_, v___x_2447_, v___x_2446_, v___x_2445_, v___x_2444_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2454_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2455_ = lean_unsigned_to_nat(34u);
v___x_2456_ = lean_unsigned_to_nat(307u);
v___x_2457_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2458_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2459_ = l_mkPanicMessageWithDecl(v___x_2458_, v___x_2457_, v___x_2456_, v___x_2455_, v___x_2454_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_discr_2467_; lean_object* v_alts_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2537_; 
v_discr_2467_ = lean_ctor_get(v_c_2460_, 2);
v_alts_2468_ = lean_ctor_get(v_c_2460_, 3);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_c_2460_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; lean_object* v_unused_2539_; 
v_unused_2538_ = lean_ctor_get(v_c_2460_, 1);
lean_dec(v_unused_2538_);
v_unused_2539_ = lean_ctor_get(v_c_2460_, 0);
lean_dec(v_unused_2539_);
v___x_2470_ = v_c_2460_;
v_isShared_2471_ = v_isSharedCheck_2537_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_alts_2468_);
lean_inc(v_discr_2467_);
lean_dec(v_c_2460_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2537_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; 
v___x_2472_ = lean_array_get_size(v_alts_2468_);
v___x_2473_ = lean_unsigned_to_nat(1u);
v___x_2474_ = lean_nat_dec_eq(v___x_2472_, v___x_2473_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_del_object(v___x_2470_);
lean_dec_ref(v_alts_2468_);
lean_dec(v_discr_2467_);
v___x_2475_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2476_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2475_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
return v___x_2476_;
}
else
{
uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = 0;
v___x_2478_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2479_ = lean_unsigned_to_nat(0u);
v___x_2480_ = lean_array_get(v___x_2478_, v_alts_2468_, v___x_2479_);
lean_dec_ref(v_alts_2468_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_params_2481_; lean_object* v_code_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2533_; 
v_params_2481_ = lean_ctor_get(v___x_2480_, 1);
v_code_2482_ = lean_ctor_get(v___x_2480_, 2);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2480_, 0);
lean_dec(v_unused_2534_);
v___x_2484_ = v___x_2480_;
v_isShared_2485_ = v_isSharedCheck_2533_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_code_2482_);
lean_inc(v_params_2481_);
lean_dec(v___x_2480_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2533_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2477_, v_params_2481_, v_a_2463_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v_fvarId_2490_; lean_object* v_binderName_2491_; lean_object* v_lctx_2492_; lean_object* v_nextIdx_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref_known(v___x_2486_, 1);
v___x_2487_ = lean_st_ref_take(v_a_2463_);
v___x_2488_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2489_ = lean_array_get(v___x_2488_, v_params_2481_, v___x_2479_);
lean_dec_ref(v_params_2481_);
v_fvarId_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_fvarId_2490_);
v_binderName_2491_ = lean_ctor_get(v___x_2489_, 1);
lean_inc(v_binderName_2491_);
lean_dec(v___x_2489_);
v_lctx_2492_ = lean_ctor_get(v___x_2487_, 0);
v_nextIdx_2493_ = lean_ctor_get(v___x_2487_, 1);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2495_ = v___x_2487_;
v_isShared_2496_ = v_isSharedCheck_2524_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_nextIdx_2493_);
lean_inc(v_lctx_2492_);
lean_dec(v___x_2487_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2524_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2497_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2499_, 0, v_discr_2467_);
v___x_2500_ = lean_mk_empty_array_with_capacity(v___x_2473_);
v___x_2501_ = lean_array_push(v___x_2500_, v___x_2499_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set_tag(v___x_2484_, 3);
lean_ctor_set(v___x_2484_, 2, v___x_2501_);
lean_ctor_set(v___x_2484_, 1, v___x_2498_);
lean_ctor_set(v___x_2484_, 0, v___x_2497_);
v___x_2503_ = v___x_2484_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2504_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 3, v___x_2503_);
lean_ctor_set(v___x_2470_, 2, v___x_2504_);
lean_ctor_set(v___x_2470_, 1, v_binderName_2491_);
lean_ctor_set(v___x_2470_, 0, v_fvarId_2490_);
v___x_2506_ = v___x_2470_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_fvarId_2490_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v_binderName_2491_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v___x_2504_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v___x_2503_);
v___x_2506_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; lean_object* v___x_2509_; 
lean_inc_ref(v___x_2506_);
v___x_2507_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2477_, v_lctx_2492_, v___x_2506_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2507_);
v___x_2509_ = v___x_2495_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2507_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_nextIdx_2493_);
v___x_2509_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_st_ref_set(v_a_2463_, v___x_2509_);
v___x_2511_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2482_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2520_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2506_);
lean_ctor_set(v___x_2516_, 1, v_a_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_dec_ref(v___x_2506_);
return v___x_2511_;
}
}
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_del_object(v___x_2484_);
lean_dec_ref(v_code_2482_);
lean_dec_ref(v_params_2481_);
lean_del_object(v___x_2470_);
lean_dec(v_discr_2467_);
v_a_2525_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2486_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2486_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v___x_2480_);
lean_del_object(v___x_2470_);
lean_dec(v_discr_2467_);
v___x_2535_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2536_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2535_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_);
return v___x_2536_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2541_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2542_ = lean_unsigned_to_nat(2u);
v___x_2543_ = lean_unsigned_to_nat(295u);
v___x_2544_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2545_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2546_ = l_mkPanicMessageWithDecl(v___x_2545_, v___x_2544_, v___x_2543_, v___x_2542_, v___x_2541_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2550_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2551_ = lean_unsigned_to_nat(34u);
v___x_2552_ = lean_unsigned_to_nat(296u);
v___x_2553_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2554_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2555_ = l_mkPanicMessageWithDecl(v___x_2554_, v___x_2553_, v___x_2552_, v___x_2551_, v___x_2550_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_discr_2563_; lean_object* v_alts_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2633_; 
v_discr_2563_ = lean_ctor_get(v_c_2556_, 2);
v_alts_2564_ = lean_ctor_get(v_c_2556_, 3);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_c_2556_);
if (v_isSharedCheck_2633_ == 0)
{
lean_object* v_unused_2634_; lean_object* v_unused_2635_; 
v_unused_2634_ = lean_ctor_get(v_c_2556_, 1);
lean_dec(v_unused_2634_);
v_unused_2635_ = lean_ctor_get(v_c_2556_, 0);
lean_dec(v_unused_2635_);
v___x_2566_ = v_c_2556_;
v_isShared_2567_ = v_isSharedCheck_2633_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_alts_2564_);
lean_inc(v_discr_2563_);
lean_dec(v_c_2556_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2633_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = lean_array_get_size(v_alts_2564_);
v___x_2569_ = lean_unsigned_to_nat(1u);
v___x_2570_ = lean_nat_dec_eq(v___x_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_del_object(v___x_2566_);
lean_dec_ref(v_alts_2564_);
lean_dec(v_discr_2563_);
v___x_2571_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2572_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2571_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
return v___x_2572_;
}
else
{
uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2573_ = 0;
v___x_2574_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2575_ = lean_unsigned_to_nat(0u);
v___x_2576_ = lean_array_get(v___x_2574_, v_alts_2564_, v___x_2575_);
lean_dec_ref(v_alts_2564_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_params_2577_; lean_object* v_code_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2629_; 
v_params_2577_ = lean_ctor_get(v___x_2576_, 1);
v_code_2578_ = lean_ctor_get(v___x_2576_, 2);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v___x_2576_, 0);
lean_dec(v_unused_2630_);
v___x_2580_ = v___x_2576_;
v_isShared_2581_ = v_isSharedCheck_2629_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_code_2578_);
lean_inc(v_params_2577_);
lean_dec(v___x_2576_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2629_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2573_, v_params_2577_, v_a_2559_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v_fvarId_2586_; lean_object* v_binderName_2587_; lean_object* v_lctx_2588_; lean_object* v_nextIdx_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref_known(v___x_2582_, 1);
v___x_2583_ = lean_st_ref_take(v_a_2559_);
v___x_2584_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2585_ = lean_array_get(v___x_2584_, v_params_2577_, v___x_2575_);
lean_dec_ref(v_params_2577_);
v_fvarId_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_fvarId_2586_);
v_binderName_2587_ = lean_ctor_get(v___x_2585_, 1);
lean_inc(v_binderName_2587_);
lean_dec(v___x_2585_);
v_lctx_2588_ = lean_ctor_get(v___x_2583_, 0);
v_nextIdx_2589_ = lean_ctor_get(v___x_2583_, 1);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2591_ = v___x_2583_;
v_isShared_2592_ = v_isSharedCheck_2620_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_nextIdx_2589_);
lean_inc(v_lctx_2588_);
lean_dec(v___x_2583_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2620_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2593_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2594_ = lean_box(0);
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v_discr_2563_);
v___x_2596_ = lean_mk_empty_array_with_capacity(v___x_2569_);
v___x_2597_ = lean_array_push(v___x_2596_, v___x_2595_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 3);
lean_ctor_set(v___x_2580_, 2, v___x_2597_);
lean_ctor_set(v___x_2580_, 1, v___x_2594_);
lean_ctor_set(v___x_2580_, 0, v___x_2593_);
v___x_2599_ = v___x_2580_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2594_);
lean_ctor_set(v_reuseFailAlloc_2619_, 2, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2600_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 3, v___x_2599_);
lean_ctor_set(v___x_2566_, 2, v___x_2600_);
lean_ctor_set(v___x_2566_, 1, v_binderName_2587_);
lean_ctor_set(v___x_2566_, 0, v_fvarId_2586_);
v___x_2602_ = v___x_2566_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_fvarId_2586_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_binderName_2587_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v___x_2599_);
v___x_2602_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_inc_ref(v___x_2602_);
v___x_2603_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2573_, v_lctx_2588_, v___x_2602_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2603_);
v___x_2605_ = v___x_2591_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_nextIdx_2589_);
v___x_2605_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_st_ref_set(v_a_2559_, v___x_2605_);
v___x_2607_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2578_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2616_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2612_; lean_object* v___x_2614_; 
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2602_);
lean_ctor_set(v___x_2612_, 1, v_a_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v___x_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
lean_dec_ref(v___x_2602_);
return v___x_2607_;
}
}
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_del_object(v___x_2580_);
lean_dec_ref(v_code_2578_);
lean_dec_ref(v_params_2577_);
lean_del_object(v___x_2566_);
lean_dec(v_discr_2563_);
v_a_2621_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2582_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2582_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_dec(v___x_2576_);
lean_del_object(v___x_2566_);
lean_dec(v_discr_2563_);
v___x_2631_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2632_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2631_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
return v___x_2632_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2637_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2638_ = lean_unsigned_to_nat(2u);
v___x_2639_ = lean_unsigned_to_nat(284u);
v___x_2640_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2641_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2642_ = l_mkPanicMessageWithDecl(v___x_2641_, v___x_2640_, v___x_2639_, v___x_2638_, v___x_2637_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2647_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2648_ = lean_unsigned_to_nat(34u);
v___x_2649_ = lean_unsigned_to_nat(285u);
v___x_2650_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2651_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2652_ = l_mkPanicMessageWithDecl(v___x_2651_, v___x_2650_, v___x_2649_, v___x_2648_, v___x_2647_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_discr_2660_; lean_object* v_alts_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2730_; 
v_discr_2660_ = lean_ctor_get(v_c_2653_, 2);
v_alts_2661_ = lean_ctor_get(v_c_2653_, 3);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_c_2653_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; lean_object* v_unused_2732_; 
v_unused_2731_ = lean_ctor_get(v_c_2653_, 1);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_c_2653_, 0);
lean_dec(v_unused_2732_);
v___x_2663_ = v_c_2653_;
v_isShared_2664_ = v_isSharedCheck_2730_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_alts_2661_);
lean_inc(v_discr_2660_);
lean_dec(v_c_2653_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2730_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_array_get_size(v_alts_2661_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_del_object(v___x_2663_);
lean_dec_ref(v_alts_2661_);
lean_dec(v_discr_2660_);
v___x_2668_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2669_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2668_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
return v___x_2669_;
}
else
{
uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2670_ = 0;
v___x_2671_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_array_get(v___x_2671_, v_alts_2661_, v___x_2672_);
lean_dec_ref(v_alts_2661_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_params_2674_; lean_object* v_code_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2726_; 
v_params_2674_ = lean_ctor_get(v___x_2673_, 1);
v_code_2675_ = lean_ctor_get(v___x_2673_, 2);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; 
v_unused_2727_ = lean_ctor_get(v___x_2673_, 0);
lean_dec(v_unused_2727_);
v___x_2677_ = v___x_2673_;
v_isShared_2678_ = v_isSharedCheck_2726_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_code_2675_);
lean_inc(v_params_2674_);
lean_dec(v___x_2673_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2726_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2670_, v_params_2674_, v_a_2656_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_fvarId_2683_; lean_object* v_binderName_2684_; lean_object* v_lctx_2685_; lean_object* v_nextIdx_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref_known(v___x_2679_, 1);
v___x_2680_ = lean_st_ref_take(v_a_2656_);
v___x_2681_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2682_ = lean_array_get(v___x_2681_, v_params_2674_, v___x_2672_);
lean_dec_ref(v_params_2674_);
v_fvarId_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_fvarId_2683_);
v_binderName_2684_ = lean_ctor_get(v___x_2682_, 1);
lean_inc(v_binderName_2684_);
lean_dec(v___x_2682_);
v_lctx_2685_ = lean_ctor_get(v___x_2680_, 0);
v_nextIdx_2686_ = lean_ctor_get(v___x_2680_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2688_ = v___x_2680_;
v_isShared_2689_ = v_isSharedCheck_2717_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_nextIdx_2686_);
lean_inc(v_lctx_2685_);
lean_dec(v___x_2680_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2717_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2690_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_discr_2660_);
v___x_2693_ = lean_mk_empty_array_with_capacity(v___x_2666_);
v___x_2694_ = lean_array_push(v___x_2693_, v___x_2692_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 3);
lean_ctor_set(v___x_2677_, 2, v___x_2694_);
lean_ctor_set(v___x_2677_, 1, v___x_2691_);
lean_ctor_set(v___x_2677_, 0, v___x_2690_);
v___x_2696_ = v___x_2677_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2716_, 2, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 3, v___x_2696_);
lean_ctor_set(v___x_2663_, 2, v___x_2697_);
lean_ctor_set(v___x_2663_, 1, v_binderName_2684_);
lean_ctor_set(v___x_2663_, 0, v_fvarId_2683_);
v___x_2699_ = v___x_2663_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_fvarId_2683_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v_binderName_2684_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2715_, 3, v___x_2696_);
v___x_2699_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2702_; 
lean_inc_ref(v___x_2699_);
v___x_2700_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2670_, v_lctx_2685_, v___x_2699_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2700_);
v___x_2702_ = v___x_2688_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_nextIdx_2686_);
v___x_2702_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_st_ref_set(v_a_2656_, v___x_2702_);
v___x_2704_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2675_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_a_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2713_; 
v_a_2705_ = lean_ctor_get(v___x_2704_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2707_ = v___x_2704_;
v_isShared_2708_ = v_isSharedCheck_2713_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_a_2705_);
lean_dec(v___x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2713_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2699_);
lean_ctor_set(v___x_2709_, 1, v_a_2705_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 0, v___x_2709_);
v___x_2711_ = v___x_2707_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
else
{
lean_dec_ref(v___x_2699_);
return v___x_2704_;
}
}
}
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_del_object(v___x_2677_);
lean_dec_ref(v_code_2675_);
lean_dec_ref(v_params_2674_);
lean_del_object(v___x_2663_);
lean_dec(v_discr_2660_);
v_a_2718_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2679_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2679_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec(v___x_2673_);
lean_del_object(v___x_2663_);
lean_dec(v_discr_2660_);
v___x_2728_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2729_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2728_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
return v___x_2729_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2734_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2735_ = lean_unsigned_to_nat(2u);
v___x_2736_ = lean_unsigned_to_nat(273u);
v___x_2737_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2738_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2739_ = l_mkPanicMessageWithDecl(v___x_2738_, v___x_2737_, v___x_2736_, v___x_2735_, v___x_2734_);
return v___x_2739_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2744_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2745_ = lean_unsigned_to_nat(34u);
v___x_2746_ = lean_unsigned_to_nat(274u);
v___x_2747_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2748_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2749_ = l_mkPanicMessageWithDecl(v___x_2748_, v___x_2747_, v___x_2746_, v___x_2745_, v___x_2744_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_discr_2757_; lean_object* v_alts_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2827_; 
v_discr_2757_ = lean_ctor_get(v_c_2750_, 2);
v_alts_2758_ = lean_ctor_get(v_c_2750_, 3);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_c_2750_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; lean_object* v_unused_2829_; 
v_unused_2828_ = lean_ctor_get(v_c_2750_, 1);
lean_dec(v_unused_2828_);
v_unused_2829_ = lean_ctor_get(v_c_2750_, 0);
lean_dec(v_unused_2829_);
v___x_2760_ = v_c_2750_;
v_isShared_2761_ = v_isSharedCheck_2827_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_alts_2758_);
lean_inc(v_discr_2757_);
lean_dec(v_c_2750_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2827_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2762_ = lean_array_get_size(v_alts_2758_);
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_nat_dec_eq(v___x_2762_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_del_object(v___x_2760_);
lean_dec_ref(v_alts_2758_);
lean_dec(v_discr_2757_);
v___x_2765_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2766_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2765_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
return v___x_2766_;
}
else
{
uint8_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2767_ = 0;
v___x_2768_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = lean_array_get(v___x_2768_, v_alts_2758_, v___x_2769_);
lean_dec_ref(v_alts_2758_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_params_2771_; lean_object* v_code_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2823_; 
v_params_2771_ = lean_ctor_get(v___x_2770_, 1);
v_code_2772_ = lean_ctor_get(v___x_2770_, 2);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2770_, 0);
lean_dec(v_unused_2824_);
v___x_2774_ = v___x_2770_;
v_isShared_2775_ = v_isSharedCheck_2823_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_code_2772_);
lean_inc(v_params_2771_);
lean_dec(v___x_2770_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2823_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2767_, v_params_2771_, v_a_2753_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v_fvarId_2780_; lean_object* v_binderName_2781_; lean_object* v_lctx_2782_; lean_object* v_nextIdx_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref_known(v___x_2776_, 1);
v___x_2777_ = lean_st_ref_take(v_a_2753_);
v___x_2778_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2779_ = lean_array_get(v___x_2778_, v_params_2771_, v___x_2769_);
lean_dec_ref(v_params_2771_);
v_fvarId_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_fvarId_2780_);
v_binderName_2781_ = lean_ctor_get(v___x_2779_, 1);
lean_inc(v_binderName_2781_);
lean_dec(v___x_2779_);
v_lctx_2782_ = lean_ctor_get(v___x_2777_, 0);
v_nextIdx_2783_ = lean_ctor_get(v___x_2777_, 1);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2785_ = v___x_2777_;
v_isShared_2786_ = v_isSharedCheck_2814_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_nextIdx_2783_);
lean_inc(v_lctx_2782_);
lean_dec(v___x_2777_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2814_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2787_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2788_ = lean_box(0);
v___x_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_discr_2757_);
v___x_2790_ = lean_mk_empty_array_with_capacity(v___x_2763_);
v___x_2791_ = lean_array_push(v___x_2790_, v___x_2789_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set_tag(v___x_2774_, 3);
lean_ctor_set(v___x_2774_, 2, v___x_2791_);
lean_ctor_set(v___x_2774_, 1, v___x_2788_);
lean_ctor_set(v___x_2774_, 0, v___x_2787_);
v___x_2793_ = v___x_2774_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v___x_2787_);
lean_ctor_set(v_reuseFailAlloc_2813_, 1, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2813_, 2, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2794_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 3, v___x_2793_);
lean_ctor_set(v___x_2760_, 2, v___x_2794_);
lean_ctor_set(v___x_2760_, 1, v_binderName_2781_);
lean_ctor_set(v___x_2760_, 0, v_fvarId_2780_);
v___x_2796_ = v___x_2760_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_fvarId_2780_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_binderName_2781_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v___x_2793_);
v___x_2796_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_inc_ref(v___x_2796_);
v___x_2797_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2767_, v_lctx_2782_, v___x_2796_);
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v___x_2797_);
v___x_2799_ = v___x_2785_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v_nextIdx_2783_);
v___x_2799_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_st_ref_set(v_a_2753_, v___x_2799_);
v___x_2801_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2772_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2810_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2810_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2796_);
lean_ctor_set(v___x_2806_, 1, v_a_2802_);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2806_);
v___x_2808_ = v___x_2804_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
else
{
lean_dec_ref(v___x_2796_);
return v___x_2801_;
}
}
}
}
}
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_del_object(v___x_2774_);
lean_dec_ref(v_code_2772_);
lean_dec_ref(v_params_2771_);
lean_del_object(v___x_2760_);
lean_dec(v_discr_2757_);
v_a_2815_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2776_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2776_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v___x_2770_);
lean_del_object(v___x_2760_);
lean_dec(v_discr_2757_);
v___x_2825_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2826_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2825_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
return v___x_2826_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2831_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2832_ = lean_unsigned_to_nat(2u);
v___x_2833_ = lean_unsigned_to_nat(261u);
v___x_2834_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2835_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2836_ = l_mkPanicMessageWithDecl(v___x_2835_, v___x_2834_, v___x_2833_, v___x_2832_, v___x_2831_);
return v___x_2836_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2840_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2841_ = lean_unsigned_to_nat(34u);
v___x_2842_ = lean_unsigned_to_nat(262u);
v___x_2843_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2844_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2845_ = l_mkPanicMessageWithDecl(v___x_2844_, v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_discr_2853_; lean_object* v_alts_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2923_; 
v_discr_2853_ = lean_ctor_get(v_c_2846_, 2);
v_alts_2854_ = lean_ctor_get(v_c_2846_, 3);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_c_2846_);
if (v_isSharedCheck_2923_ == 0)
{
lean_object* v_unused_2924_; lean_object* v_unused_2925_; 
v_unused_2924_ = lean_ctor_get(v_c_2846_, 1);
lean_dec(v_unused_2924_);
v_unused_2925_ = lean_ctor_get(v_c_2846_, 0);
lean_dec(v_unused_2925_);
v___x_2856_ = v_c_2846_;
v_isShared_2857_ = v_isSharedCheck_2923_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_alts_2854_);
lean_inc(v_discr_2853_);
lean_dec(v_c_2846_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2923_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2858_ = lean_array_get_size(v_alts_2854_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_dec_eq(v___x_2858_, v___x_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_del_object(v___x_2856_);
lean_dec_ref(v_alts_2854_);
lean_dec(v_discr_2853_);
v___x_2861_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2862_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2861_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
return v___x_2862_;
}
else
{
uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2863_ = 0;
v___x_2864_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2865_ = lean_unsigned_to_nat(0u);
v___x_2866_ = lean_array_get(v___x_2864_, v_alts_2854_, v___x_2865_);
lean_dec_ref(v_alts_2854_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_params_2867_; lean_object* v_code_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2919_; 
v_params_2867_ = lean_ctor_get(v___x_2866_, 1);
v_code_2868_ = lean_ctor_get(v___x_2866_, 2);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2866_, 0);
lean_dec(v_unused_2920_);
v___x_2870_ = v___x_2866_;
v_isShared_2871_ = v_isSharedCheck_2919_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_code_2868_);
lean_inc(v_params_2867_);
lean_dec(v___x_2866_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2919_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2863_, v_params_2867_, v_a_2849_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v_fvarId_2876_; lean_object* v_binderName_2877_; lean_object* v_lctx_2878_; lean_object* v_nextIdx_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref_known(v___x_2872_, 1);
v___x_2873_ = lean_st_ref_take(v_a_2849_);
v___x_2874_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2875_ = lean_array_get(v___x_2874_, v_params_2867_, v___x_2865_);
lean_dec_ref(v_params_2867_);
v_fvarId_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_fvarId_2876_);
v_binderName_2877_ = lean_ctor_get(v___x_2875_, 1);
lean_inc(v_binderName_2877_);
lean_dec(v___x_2875_);
v_lctx_2878_ = lean_ctor_get(v___x_2873_, 0);
v_nextIdx_2879_ = lean_ctor_get(v___x_2873_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2881_ = v___x_2873_;
v_isShared_2882_ = v_isSharedCheck_2910_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_nextIdx_2879_);
lean_inc(v_lctx_2878_);
lean_dec(v___x_2873_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2910_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2883_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2884_ = lean_box(0);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_discr_2853_);
v___x_2886_ = lean_mk_empty_array_with_capacity(v___x_2859_);
v___x_2887_ = lean_array_push(v___x_2886_, v___x_2885_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set_tag(v___x_2870_, 3);
lean_ctor_set(v___x_2870_, 2, v___x_2887_);
lean_ctor_set(v___x_2870_, 1, v___x_2884_);
lean_ctor_set(v___x_2870_, 0, v___x_2883_);
v___x_2889_ = v___x_2870_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2884_);
lean_ctor_set(v_reuseFailAlloc_2909_, 2, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 3, v___x_2889_);
lean_ctor_set(v___x_2856_, 2, v___x_2890_);
lean_ctor_set(v___x_2856_, 1, v_binderName_2877_);
lean_ctor_set(v___x_2856_, 0, v_fvarId_2876_);
v___x_2892_ = v___x_2856_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_fvarId_2876_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_binderName_2877_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2908_, 3, v___x_2889_);
v___x_2892_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_inc_ref(v___x_2892_);
v___x_2893_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2863_, v_lctx_2878_, v___x_2892_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2893_);
v___x_2895_ = v___x_2881_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_nextIdx_2879_);
v___x_2895_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_st_ref_set(v_a_2849_, v___x_2895_);
v___x_2897_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2868_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2906_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2892_);
lean_ctor_set(v___x_2902_, 1, v_a_2898_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
lean_dec_ref(v___x_2892_);
return v___x_2897_;
}
}
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_del_object(v___x_2870_);
lean_dec_ref(v_code_2868_);
lean_dec_ref(v_params_2867_);
lean_del_object(v___x_2856_);
lean_dec(v_discr_2853_);
v_a_2911_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2872_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2872_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_dec(v___x_2866_);
lean_del_object(v___x_2856_);
lean_dec(v_discr_2853_);
v___x_2921_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2922_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2921_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
return v___x_2922_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2927_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2928_ = lean_unsigned_to_nat(2u);
v___x_2929_ = lean_unsigned_to_nat(249u);
v___x_2930_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2931_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2932_ = l_mkPanicMessageWithDecl(v___x_2931_, v___x_2930_, v___x_2929_, v___x_2928_, v___x_2927_);
return v___x_2932_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2937_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_2938_ = lean_unsigned_to_nat(34u);
v___x_2939_ = lean_unsigned_to_nat(250u);
v___x_2940_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2941_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_2942_ = l_mkPanicMessageWithDecl(v___x_2941_, v___x_2940_, v___x_2939_, v___x_2938_, v___x_2937_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_discr_2950_; lean_object* v_alts_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3020_; 
v_discr_2950_ = lean_ctor_get(v_c_2943_, 2);
v_alts_2951_ = lean_ctor_get(v_c_2943_, 3);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_c_2943_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; lean_object* v_unused_3022_; 
v_unused_3021_ = lean_ctor_get(v_c_2943_, 1);
lean_dec(v_unused_3021_);
v_unused_3022_ = lean_ctor_get(v_c_2943_, 0);
lean_dec(v_unused_3022_);
v___x_2953_ = v_c_2943_;
v_isShared_2954_ = v_isSharedCheck_3020_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_alts_2951_);
lean_inc(v_discr_2950_);
lean_dec(v_c_2943_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3020_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; uint8_t v___x_2957_; 
v___x_2955_ = lean_array_get_size(v_alts_2951_);
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_dec_eq(v___x_2955_, v___x_2956_);
if (v___x_2957_ == 0)
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_del_object(v___x_2953_);
lean_dec_ref(v_alts_2951_);
lean_dec(v_discr_2950_);
v___x_2958_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2959_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2958_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_2959_;
}
else
{
uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2960_ = 0;
v___x_2961_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2962_ = lean_unsigned_to_nat(0u);
v___x_2963_ = lean_array_get(v___x_2961_, v_alts_2951_, v___x_2962_);
lean_dec_ref(v_alts_2951_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_params_2964_; lean_object* v_code_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_3016_; 
v_params_2964_ = lean_ctor_get(v___x_2963_, 1);
v_code_2965_ = lean_ctor_get(v___x_2963_, 2);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_2963_, 0);
lean_dec(v_unused_3017_);
v___x_2967_ = v___x_2963_;
v_isShared_2968_ = v_isSharedCheck_3016_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_code_2965_);
lean_inc(v_params_2964_);
lean_dec(v___x_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_3016_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2960_, v_params_2964_, v_a_2946_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_fvarId_2973_; lean_object* v_binderName_2974_; lean_object* v_lctx_2975_; lean_object* v_nextIdx_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref_known(v___x_2969_, 1);
v___x_2970_ = lean_st_ref_take(v_a_2946_);
v___x_2971_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2972_ = lean_array_get(v___x_2971_, v_params_2964_, v___x_2962_);
lean_dec_ref(v_params_2964_);
v_fvarId_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_fvarId_2973_);
v_binderName_2974_ = lean_ctor_get(v___x_2972_, 1);
lean_inc(v_binderName_2974_);
lean_dec(v___x_2972_);
v_lctx_2975_ = lean_ctor_get(v___x_2970_, 0);
v_nextIdx_2976_ = lean_ctor_get(v___x_2970_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2978_ = v___x_2970_;
v_isShared_2979_ = v_isSharedCheck_3007_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_nextIdx_2976_);
lean_inc(v_lctx_2975_);
lean_dec(v___x_2970_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3007_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2980_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2982_, 0, v_discr_2950_);
v___x_2983_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2984_ = lean_array_push(v___x_2983_, v___x_2982_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set_tag(v___x_2967_, 3);
lean_ctor_set(v___x_2967_, 2, v___x_2984_);
lean_ctor_set(v___x_2967_, 1, v___x_2981_);
lean_ctor_set(v___x_2967_, 0, v___x_2980_);
v___x_2986_ = v___x_2967_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2987_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 3, v___x_2986_);
lean_ctor_set(v___x_2953_, 2, v___x_2987_);
lean_ctor_set(v___x_2953_, 1, v_binderName_2974_);
lean_ctor_set(v___x_2953_, 0, v_fvarId_2973_);
v___x_2989_ = v___x_2953_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_fvarId_2973_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_binderName_2974_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v___x_2986_);
v___x_2989_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_inc_ref(v___x_2989_);
v___x_2990_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2960_, v_lctx_2975_, v___x_2989_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2990_);
v___x_2992_ = v___x_2978_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_nextIdx_2976_);
v___x_2992_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_st_ref_set(v_a_2946_, v___x_2992_);
v___x_2994_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2965_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3003_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3003_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2989_);
lean_ctor_set(v___x_2999_, 1, v_a_2995_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_2999_);
v___x_3001_ = v___x_2997_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
else
{
lean_dec_ref(v___x_2989_);
return v___x_2994_;
}
}
}
}
}
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_del_object(v___x_2967_);
lean_dec_ref(v_code_2965_);
lean_dec_ref(v_params_2964_);
lean_del_object(v___x_2953_);
lean_dec(v_discr_2950_);
v_a_3008_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_2969_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_2969_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec(v___x_2963_);
lean_del_object(v___x_2953_);
lean_dec(v_discr_2950_);
v___x_3018_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_3019_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3018_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
return v___x_3019_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3024_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_3025_ = lean_unsigned_to_nat(2u);
v___x_3026_ = lean_unsigned_to_nat(238u);
v___x_3027_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3028_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_3029_ = l_mkPanicMessageWithDecl(v___x_3028_, v___x_3027_, v___x_3026_, v___x_3025_, v___x_3024_);
return v___x_3029_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3031_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_3032_ = lean_unsigned_to_nat(34u);
v___x_3033_ = lean_unsigned_to_nat(239u);
v___x_3034_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3035_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__19));
v___x_3036_ = l_mkPanicMessageWithDecl(v___x_3035_, v___x_3034_, v___x_3033_, v___x_3032_, v___x_3031_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_3037_, lean_object* v_uintName_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_discr_3045_; lean_object* v_alts_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3116_; 
v_discr_3045_ = lean_ctor_get(v_c_3037_, 2);
v_alts_3046_ = lean_ctor_get(v_c_3037_, 3);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_c_3037_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; lean_object* v_unused_3118_; 
v_unused_3117_ = lean_ctor_get(v_c_3037_, 1);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_c_3037_, 0);
lean_dec(v_unused_3118_);
v___x_3048_ = v_c_3037_;
v_isShared_3049_ = v_isSharedCheck_3116_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_alts_3046_);
lean_inc(v_discr_3045_);
lean_dec(v_c_3037_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3116_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3050_ = lean_array_get_size(v_alts_3046_);
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_nat_dec_eq(v___x_3050_, v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_del_object(v___x_3048_);
lean_dec_ref(v_alts_3046_);
lean_dec(v_discr_3045_);
lean_dec(v_uintName_3038_);
v___x_3053_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_3054_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3053_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
return v___x_3054_;
}
else
{
uint8_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3055_ = 0;
v___x_3056_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_array_get(v___x_3056_, v_alts_3046_, v___x_3057_);
lean_dec_ref(v_alts_3046_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_params_3059_; lean_object* v_code_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3112_; 
v_params_3059_ = lean_ctor_get(v___x_3058_, 1);
v_code_3060_ = lean_ctor_get(v___x_3058_, 2);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v___x_3058_, 0);
lean_dec(v_unused_3113_);
v___x_3062_ = v___x_3058_;
v_isShared_3063_ = v_isSharedCheck_3112_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_code_3060_);
lean_inc(v_params_3059_);
lean_dec(v___x_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3112_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3055_, v_params_3059_, v_a_3041_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v_fvarId_3068_; lean_object* v_binderName_3069_; lean_object* v_lctx_3070_; lean_object* v_nextIdx_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref_known(v___x_3064_, 1);
v___x_3065_ = lean_st_ref_take(v_a_3041_);
v___x_3066_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3067_ = lean_array_get(v___x_3066_, v_params_3059_, v___x_3057_);
lean_dec_ref(v_params_3059_);
v_fvarId_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_fvarId_3068_);
v_binderName_3069_ = lean_ctor_get(v___x_3067_, 1);
lean_inc(v_binderName_3069_);
lean_dec(v___x_3067_);
v_lctx_3070_ = lean_ctor_get(v___x_3065_, 0);
v_nextIdx_3071_ = lean_ctor_get(v___x_3065_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3073_ = v___x_3065_;
v_isShared_3074_ = v_isSharedCheck_3103_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_nextIdx_3071_);
lean_inc(v_lctx_3070_);
lean_dec(v___x_3065_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3103_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3075_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3));
v___x_3076_ = l_Lean_Name_str___override(v_uintName_3038_, v___x_3075_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_discr_3045_);
v___x_3079_ = lean_mk_empty_array_with_capacity(v___x_3051_);
v___x_3080_ = lean_array_push(v___x_3079_, v___x_3078_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set_tag(v___x_3062_, 3);
lean_ctor_set(v___x_3062_, 2, v___x_3080_);
lean_ctor_set(v___x_3062_, 1, v___x_3077_);
lean_ctor_set(v___x_3062_, 0, v___x_3076_);
v___x_3082_ = v___x_3062_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 3, v___x_3082_);
lean_ctor_set(v___x_3048_, 2, v___x_3083_);
lean_ctor_set(v___x_3048_, 1, v_binderName_3069_);
lean_ctor_set(v___x_3048_, 0, v_fvarId_3068_);
v___x_3085_ = v___x_3048_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_fvarId_3068_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_binderName_3069_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3101_, 3, v___x_3082_);
v___x_3085_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
lean_inc_ref(v___x_3085_);
v___x_3086_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3055_, v_lctx_3070_, v___x_3085_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 0, v___x_3086_);
v___x_3088_ = v___x_3073_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_nextIdx_3071_);
v___x_3088_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_st_ref_set(v_a_3041_, v___x_3088_);
v___x_3090_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3060_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3099_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3093_ = v___x_3090_;
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3090_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3099_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3085_);
lean_ctor_set(v___x_3095_, 1, v_a_3091_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3095_);
v___x_3097_ = v___x_3093_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_dec_ref(v___x_3085_);
return v___x_3090_;
}
}
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_del_object(v___x_3062_);
lean_dec_ref(v_code_3060_);
lean_dec_ref(v_params_3059_);
lean_del_object(v___x_3048_);
lean_dec(v_discr_3045_);
lean_dec(v_uintName_3038_);
v_a_3104_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3064_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3064_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec(v___x_3058_);
lean_del_object(v___x_3048_);
lean_dec(v_discr_3045_);
lean_dec(v_uintName_3038_);
v___x_3114_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4);
v___x_3115_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3114_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
return v___x_3115_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3119_ = lean_box(0);
v___x_3120_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3121_ = l_Lean_mkConst(v___x_3120_, v___x_3119_);
return v___x_3121_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = lean_box(0);
v___x_3129_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3130_ = l_Lean_mkConst(v___x_3129_, v___x_3128_);
return v___x_3130_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3140_ = l_Lean_mkConst(v___x_3139_, v___x_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_3165_, size_t v_sz_3166_, size_t v_i_3167_, lean_object* v_bs_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v___x_3175_; 
v___x_3175_ = lean_usize_dec_lt(v_i_3167_, v_sz_3166_);
if (v___x_3175_ == 0)
{
lean_object* v___x_3176_; 
lean_dec(v___x_3165_);
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_bs_3168_);
return v___x_3176_;
}
else
{
lean_object* v_v_3177_; lean_object* v___x_3178_; lean_object* v_bs_x27_3179_; lean_object* v_a_3181_; 
v_v_3177_ = lean_array_uget(v_bs_3168_, v_i_3167_);
v___x_3178_ = lean_unsigned_to_nat(0u);
v_bs_x27_3179_ = lean_array_uset(v_bs_3168_, v_i_3167_, v___x_3178_);
if (lean_obj_tag(v_v_3177_) == 0)
{
lean_object* v_ctorName_3186_; lean_object* v_params_3187_; lean_object* v_code_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3315_; 
v_ctorName_3186_ = lean_ctor_get(v_v_3177_, 0);
v_params_3187_ = lean_ctor_get(v_v_3177_, 1);
v_code_3188_ = lean_ctor_get(v_v_3177_, 2);
v_isSharedCheck_3315_ = !lean_is_exclusive(v_v_3177_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3190_ = v_v_3177_;
v_isShared_3191_ = v_isSharedCheck_3315_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_code_3188_);
lean_inc(v_params_3187_);
lean_inc(v_ctorName_3186_);
lean_dec(v_v_3177_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3315_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
uint8_t v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = 0;
v___x_3193_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3194_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3192_, v_params_3187_, v___y_3171_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
lean_dec_ref_known(v___x_3194_, 1);
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3197_ = lean_array_get(v___x_3193_, v_params_3187_, v___x_3178_);
lean_dec_ref(v_params_3187_);
v___x_3198_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_3199_ = lean_name_eq(v_ctorName_3186_, v___x_3198_);
lean_dec(v_ctorName_3186_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v_fvarId_3201_; lean_object* v_binderName_3202_; lean_object* v_lctx_3203_; lean_object* v_nextIdx_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3235_; 
v___x_3200_ = lean_st_ref_take(v___y_3171_);
v_fvarId_3201_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_fvarId_3201_);
v_binderName_3202_ = lean_ctor_get(v___x_3197_, 1);
lean_inc(v_binderName_3202_);
lean_dec(v___x_3197_);
v_lctx_3203_ = lean_ctor_get(v___x_3200_, 0);
v_nextIdx_3204_ = lean_ctor_get(v___x_3200_, 1);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3206_ = v___x_3200_;
v_isShared_3207_ = v_isSharedCheck_3235_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_nextIdx_3204_);
lean_inc(v_lctx_3203_);
lean_dec(v___x_3200_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3235_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_3209_ = lean_unsigned_to_nat(1u);
v___x_3210_ = lean_mk_empty_array_with_capacity(v___x_3209_);
lean_inc(v___x_3165_);
v___x_3211_ = lean_array_push(v___x_3210_, v___x_3165_);
v___x_3212_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3208_);
lean_ctor_set(v___x_3212_, 1, v___x_3195_);
lean_ctor_set(v___x_3212_, 2, v___x_3211_);
v___x_3213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3213_, 0, v_fvarId_3201_);
lean_ctor_set(v___x_3213_, 1, v_binderName_3202_);
lean_ctor_set(v___x_3213_, 2, v___x_3196_);
lean_ctor_set(v___x_3213_, 3, v___x_3212_);
lean_inc_ref(v___x_3213_);
v___x_3214_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3192_, v_lctx_3203_, v___x_3213_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3214_);
v___x_3216_ = v___x_3206_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_nextIdx_3204_);
v___x_3216_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_st_ref_set(v___y_3171_, v___x_3216_);
v___x_3218_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3188_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_3221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3213_);
lean_ctor_set(v___x_3222_, 1, v_a_3219_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 2, v___x_3222_);
lean_ctor_set(v___x_3190_, 1, v___x_3221_);
lean_ctor_set(v___x_3190_, 0, v___x_3220_);
v___x_3224_ = v___x_3190_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3221_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
v_a_3181_ = v___x_3224_;
goto v___jp_3180_;
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref_known(v___x_3213_, 4);
lean_del_object(v___x_3190_);
lean_dec_ref(v_bs_x27_3179_);
lean_dec(v___x_3165_);
v_a_3226_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3218_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3218_);
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
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_3237_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_3238_ = lean_unsigned_to_nat(1u);
v___x_3239_ = lean_mk_empty_array_with_capacity(v___x_3238_);
lean_inc(v___x_3165_);
v___x_3240_ = lean_array_push(v___x_3239_, v___x_3165_);
v___x_3241_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3237_);
lean_ctor_set(v___x_3241_, 1, v___x_3195_);
lean_ctor_set(v___x_3241_, 2, v___x_3240_);
v___x_3242_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3192_, v___x_3236_, v___x_3196_, v___x_3241_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v___x_3244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3));
v___x_3246_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3192_, v___x_3244_, v___x_3196_, v___x_3245_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v_fvarId_3248_; lean_object* v_fvarId_3249_; lean_object* v___x_3250_; lean_object* v_fvarId_3251_; lean_object* v_binderName_3252_; lean_object* v_lctx_3253_; lean_object* v_nextIdx_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3290_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v_fvarId_3248_ = lean_ctor_get(v_a_3243_, 0);
v_fvarId_3249_ = lean_ctor_get(v_a_3247_, 0);
v___x_3250_ = lean_st_ref_take(v___y_3171_);
v_fvarId_3251_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_fvarId_3251_);
v_binderName_3252_ = lean_ctor_get(v___x_3197_, 1);
lean_inc(v_binderName_3252_);
lean_dec(v___x_3197_);
v_lctx_3253_ = lean_ctor_get(v___x_3250_, 0);
v_nextIdx_3254_ = lean_ctor_get(v___x_3250_, 1);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3256_ = v___x_3250_;
v_isShared_3257_ = v_isSharedCheck_3290_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_nextIdx_3254_);
lean_inc(v_lctx_3253_);
lean_dec(v___x_3250_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3290_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3258_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5));
lean_inc(v_fvarId_3248_);
v___x_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3259_, 0, v_fvarId_3248_);
lean_inc(v_fvarId_3249_);
v___x_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3260_, 0, v_fvarId_3249_);
v___x_3261_ = lean_unsigned_to_nat(2u);
v___x_3262_ = lean_mk_empty_array_with_capacity(v___x_3261_);
v___x_3263_ = lean_array_push(v___x_3262_, v___x_3259_);
v___x_3264_ = lean_array_push(v___x_3263_, v___x_3260_);
v___x_3265_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3258_);
lean_ctor_set(v___x_3265_, 1, v___x_3195_);
lean_ctor_set(v___x_3265_, 2, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3266_, 0, v_fvarId_3251_);
lean_ctor_set(v___x_3266_, 1, v_binderName_3252_);
lean_ctor_set(v___x_3266_, 2, v___x_3196_);
lean_ctor_set(v___x_3266_, 3, v___x_3265_);
lean_inc_ref(v___x_3266_);
v___x_3267_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3192_, v_lctx_3253_, v___x_3266_);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3267_);
v___x_3269_ = v___x_3256_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_nextIdx_3254_);
v___x_3269_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = lean_st_ref_set(v___y_3171_, v___x_3269_);
v___x_3271_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3188_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3279_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v___x_3273_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
v___x_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3266_);
lean_ctor_set(v___x_3275_, 1, v_a_3272_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v_a_3247_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v_a_3243_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 2, v___x_3277_);
lean_ctor_set(v___x_3190_, 1, v___x_3274_);
lean_ctor_set(v___x_3190_, 0, v___x_3273_);
v___x_3279_ = v___x_3190_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v___x_3277_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
v_a_3181_ = v___x_3279_;
goto v___jp_3180_;
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref_known(v___x_3266_, 4);
lean_dec(v_a_3247_);
lean_dec(v_a_3243_);
lean_del_object(v___x_3190_);
lean_dec_ref(v_bs_x27_3179_);
lean_dec(v___x_3165_);
v_a_3281_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3271_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3271_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_a_3243_);
lean_dec(v___x_3197_);
lean_del_object(v___x_3190_);
lean_dec_ref(v_code_3188_);
lean_dec_ref(v_bs_x27_3179_);
lean_dec(v___x_3165_);
v_a_3291_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3246_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3246_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v___x_3197_);
lean_del_object(v___x_3190_);
lean_dec_ref(v_code_3188_);
lean_dec_ref(v_bs_x27_3179_);
lean_dec(v___x_3165_);
v_a_3299_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3242_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3242_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_del_object(v___x_3190_);
lean_dec_ref(v_code_3188_);
lean_dec_ref(v_params_3187_);
lean_dec(v_ctorName_3186_);
lean_dec_ref(v_bs_x27_3179_);
lean_dec(v___x_3165_);
v_a_3307_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3194_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3194_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v_code_3316_; lean_object* v___x_3317_; 
v_code_3316_ = lean_ctor_get(v_v_3177_, 0);
lean_inc_ref(v_code_3316_);
v___x_3317_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3316_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3177_, v_a_3318_);
v_a_3181_ = v___x_3319_;
goto v___jp_3180_;
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref_known(v_v_3177_, 1);
lean_dec_ref(v_bs_x27_3179_);
lean_dec(v___x_3165_);
v_a_3320_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3317_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3317_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
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
v___jp_3180_:
{
size_t v___x_3182_; size_t v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = ((size_t)1ULL);
v___x_3183_ = lean_usize_add(v_i_3167_, v___x_3182_);
v___x_3184_ = lean_array_uset(v_bs_x27_3179_, v_i_3167_, v_a_3181_);
v_i_3167_ = v___x_3183_;
v_bs_3168_ = v___x_3184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_){
_start:
{
lean_object* v_resultType_3335_; lean_object* v_discr_3336_; lean_object* v_alts_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3434_; 
v_resultType_3335_ = lean_ctor_get(v_c_3328_, 1);
v_discr_3336_ = lean_ctor_get(v_c_3328_, 2);
v_alts_3337_ = lean_ctor_get(v_c_3328_, 3);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_c_3328_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; 
v_unused_3435_ = lean_ctor_get(v_c_3328_, 0);
lean_dec(v_unused_3435_);
v___x_3339_ = v_c_3328_;
v_isShared_3340_ = v_isSharedCheck_3434_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_alts_3337_);
lean_inc(v_discr_3336_);
lean_inc(v_resultType_3335_);
lean_dec(v_c_3328_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3434_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3335_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = 0;
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3346_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3347_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_3348_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3343_, v___x_3346_, v___x_3345_, v___x_3347_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v_fvarId_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
v_fvarId_3350_ = lean_ctor_get(v_a_3349_, 0);
v___x_3351_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3352_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3353_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3350_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_fvarId_3350_);
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_mk_empty_array_with_capacity(v___x_3355_);
v___x_3357_ = lean_array_push(v___x_3356_, v___x_3354_);
v___x_3358_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3353_);
lean_ctor_set(v___x_3358_, 1, v___x_3344_);
lean_ctor_set(v___x_3358_, 2, v___x_3357_);
v___x_3359_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3343_, v___x_3351_, v___x_3352_, v___x_3358_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v_fvarId_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v_fvarId_3361_ = lean_ctor_get(v_a_3360_, 0);
v___x_3362_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3363_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3364_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5);
v___x_3365_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_discr_3336_);
lean_inc(v_fvarId_3361_);
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v_fvarId_3361_);
v___x_3368_ = lean_unsigned_to_nat(2u);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3368_);
lean_inc_ref(v___x_3366_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3366_);
v___x_3371_ = lean_array_push(v___x_3370_, v___x_3367_);
v___x_3372_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3365_);
lean_ctor_set(v___x_3372_, 1, v___x_3344_);
lean_ctor_set(v___x_3372_, 2, v___x_3371_);
v___x_3373_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3343_, v___x_3362_, v___x_3364_, v___x_3372_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; size_t v_sz_3375_; size_t v___x_3376_; lean_object* v___x_3377_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
lean_dec_ref_known(v___x_3373_, 1);
v_sz_3375_ = lean_array_size(v_alts_3337_);
v___x_3376_ = ((size_t)0ULL);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3366_, v_sz_3375_, v___x_3376_, v_alts_3337_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3393_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3380_ = v___x_3377_;
v_isShared_3381_ = v_isSharedCheck_3393_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3377_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3393_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v_fvarId_3382_; lean_object* v___x_3384_; 
v_fvarId_3382_ = lean_ctor_get(v_a_3374_, 0);
lean_inc(v_fvarId_3382_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 3, v_a_3378_);
lean_ctor_set(v___x_3339_, 2, v_fvarId_3382_);
lean_ctor_set(v___x_3339_, 1, v_a_3342_);
lean_ctor_set(v___x_3339_, 0, v___x_3363_);
v___x_3384_ = v___x_3339_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_a_3342_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_fvarId_3382_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_a_3378_);
v___x_3384_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3385_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_a_3374_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_a_3360_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_a_3349_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3388_);
v___x_3390_ = v___x_3380_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_a_3374_);
lean_dec(v_a_3360_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_del_object(v___x_3339_);
v_a_3394_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3377_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3377_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref_known(v___x_3366_, 1);
lean_dec(v_a_3360_);
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_del_object(v___x_3339_);
lean_dec_ref(v_alts_3337_);
v_a_3402_ = lean_ctor_get(v___x_3373_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3373_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3373_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec(v_a_3349_);
lean_dec(v_a_3342_);
lean_del_object(v___x_3339_);
lean_dec_ref(v_alts_3337_);
lean_dec(v_discr_3336_);
v_a_3410_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3359_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3359_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec(v_a_3342_);
lean_del_object(v___x_3339_);
lean_dec_ref(v_alts_3337_);
lean_dec(v_discr_3336_);
v_a_3418_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3348_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3348_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_del_object(v___x_3339_);
lean_dec_ref(v_alts_3337_);
lean_dec(v_discr_3336_);
v_a_3426_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3341_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3341_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3445_, size_t v_sz_3446_, size_t v_i_3447_, lean_object* v_bs_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_usize_dec_lt(v_i_3447_, v_sz_3446_);
if (v___x_3455_ == 0)
{
lean_object* v___x_3456_; 
lean_dec(v___x_3445_);
v___x_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3456_, 0, v_bs_3448_);
return v___x_3456_;
}
else
{
lean_object* v_v_3457_; lean_object* v___x_3458_; lean_object* v_bs_x27_3459_; lean_object* v_a_3461_; 
v_v_3457_ = lean_array_uget(v_bs_3448_, v_i_3447_);
v___x_3458_ = lean_unsigned_to_nat(0u);
v_bs_x27_3459_ = lean_array_uset(v_bs_3448_, v_i_3447_, v___x_3458_);
if (lean_obj_tag(v_v_3457_) == 0)
{
lean_object* v_ctorName_3466_; lean_object* v_params_3467_; lean_object* v_code_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3555_; 
v_ctorName_3466_ = lean_ctor_get(v_v_3457_, 0);
v_params_3467_ = lean_ctor_get(v_v_3457_, 1);
v_code_3468_ = lean_ctor_get(v_v_3457_, 2);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_v_3457_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3470_ = v_v_3457_;
v_isShared_3471_ = v_isSharedCheck_3555_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_code_3468_);
lean_inc(v_params_3467_);
lean_inc(v_ctorName_3466_);
lean_dec(v_v_3457_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3555_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
uint8_t v___x_3472_; lean_object* v___x_3473_; 
v___x_3472_ = 0;
v___x_3473_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3472_, v_params_3467_, v___y_3451_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; uint8_t v___x_3475_; 
lean_dec_ref_known(v___x_3473_, 1);
v___x_3474_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_3475_ = lean_name_eq(v_ctorName_3466_, v___x_3474_);
lean_dec(v_ctorName_3466_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref(v_params_3467_);
v___x_3476_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3468_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
v___x_3478_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 2, v_a_3477_);
lean_ctor_set(v___x_3470_, 1, v___x_3479_);
lean_ctor_set(v___x_3470_, 0, v___x_3478_);
v___x_3481_ = v___x_3470_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 2, v_a_3477_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
v_a_3461_ = v___x_3481_;
goto v___jp_3460_;
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_del_object(v___x_3470_);
lean_dec_ref(v_bs_x27_3459_);
lean_dec(v___x_3445_);
v_a_3483_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3476_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3476_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3491_ = lean_box(0);
v___x_3492_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3493_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3));
v___x_3496_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3472_, v___x_3494_, v___x_3492_, v___x_3495_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v_fvarId_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v_fvarId_3501_; lean_object* v_binderName_3502_; lean_object* v_lctx_3503_; lean_object* v_nextIdx_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3538_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v_fvarId_3498_ = lean_ctor_get(v_a_3497_, 0);
v___x_3499_ = lean_st_ref_take(v___y_3451_);
v___x_3500_ = lean_array_get(v___x_3493_, v_params_3467_, v___x_3458_);
lean_dec_ref(v_params_3467_);
v_fvarId_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_fvarId_3501_);
v_binderName_3502_ = lean_ctor_get(v___x_3500_, 1);
lean_inc(v_binderName_3502_);
lean_dec(v___x_3500_);
v_lctx_3503_ = lean_ctor_get(v___x_3499_, 0);
v_nextIdx_3504_ = lean_ctor_get(v___x_3499_, 1);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3506_ = v___x_3499_;
v_isShared_3507_ = v_isSharedCheck_3538_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_nextIdx_3504_);
lean_inc(v_lctx_3503_);
lean_dec(v___x_3499_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3538_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5));
lean_inc(v_fvarId_3498_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_fvarId_3498_);
v___x_3510_ = lean_unsigned_to_nat(2u);
v___x_3511_ = lean_mk_empty_array_with_capacity(v___x_3510_);
lean_inc(v___x_3445_);
v___x_3512_ = lean_array_push(v___x_3511_, v___x_3445_);
v___x_3513_ = lean_array_push(v___x_3512_, v___x_3509_);
v___x_3514_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3508_);
lean_ctor_set(v___x_3514_, 1, v___x_3491_);
lean_ctor_set(v___x_3514_, 2, v___x_3513_);
v___x_3515_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3515_, 0, v_fvarId_3501_);
lean_ctor_set(v___x_3515_, 1, v_binderName_3502_);
lean_ctor_set(v___x_3515_, 2, v___x_3492_);
lean_ctor_set(v___x_3515_, 3, v___x_3514_);
lean_inc_ref(v___x_3515_);
v___x_3516_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3472_, v_lctx_3503_, v___x_3515_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3516_);
v___x_3518_ = v___x_3506_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_nextIdx_3504_);
v___x_3518_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_st_ref_set(v___y_3451_, v___x_3518_);
v___x_3520_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3468_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
v___x_3522_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_3523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3515_);
lean_ctor_set(v___x_3524_, 1, v_a_3521_);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_a_3497_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 2, v___x_3525_);
lean_ctor_set(v___x_3470_, 1, v___x_3523_);
lean_ctor_set(v___x_3470_, 0, v___x_3522_);
v___x_3527_ = v___x_3470_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3528_, 1, v___x_3523_);
lean_ctor_set(v_reuseFailAlloc_3528_, 2, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
v_a_3461_ = v___x_3527_;
goto v___jp_3460_;
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref_known(v___x_3515_, 4);
lean_dec(v_a_3497_);
lean_del_object(v___x_3470_);
lean_dec_ref(v_bs_x27_3459_);
lean_dec(v___x_3445_);
v_a_3529_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3520_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3520_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_del_object(v___x_3470_);
lean_dec_ref(v_code_3468_);
lean_dec_ref(v_params_3467_);
lean_dec_ref(v_bs_x27_3459_);
lean_dec(v___x_3445_);
v_a_3539_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3496_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3496_);
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
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_del_object(v___x_3470_);
lean_dec_ref(v_code_3468_);
lean_dec_ref(v_params_3467_);
lean_dec(v_ctorName_3466_);
lean_dec_ref(v_bs_x27_3459_);
lean_dec(v___x_3445_);
v_a_3547_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3473_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3473_);
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
}
else
{
lean_object* v_code_3556_; lean_object* v___x_3557_; 
v_code_3556_ = lean_ctor_get(v_v_3457_, 0);
lean_inc_ref(v_code_3556_);
v___x_3557_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3556_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3457_, v_a_3558_);
v_a_3461_ = v___x_3559_;
goto v___jp_3460_;
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec_ref_known(v_v_3457_, 1);
lean_dec_ref(v_bs_x27_3459_);
lean_dec(v___x_3445_);
v_a_3560_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3557_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3557_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
v___jp_3460_:
{
size_t v___x_3462_; size_t v___x_3463_; lean_object* v___x_3464_; 
v___x_3462_ = ((size_t)1ULL);
v___x_3463_ = lean_usize_add(v_i_3447_, v___x_3462_);
v___x_3464_ = lean_array_uset(v_bs_x27_3459_, v_i_3447_, v_a_3461_);
v_i_3447_ = v___x_3463_;
v_bs_3448_ = v___x_3464_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_resultType_3575_; lean_object* v_discr_3576_; lean_object* v_alts_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3654_; 
v_resultType_3575_ = lean_ctor_get(v_c_3568_, 1);
v_discr_3576_ = lean_ctor_get(v_c_3568_, 2);
v_alts_3577_ = lean_ctor_get(v_c_3568_, 3);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_c_3568_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v_c_3568_, 0);
lean_dec(v_unused_3655_);
v___x_3579_ = v_c_3568_;
v_isShared_3580_ = v_isSharedCheck_3654_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_alts_3577_);
lean_inc(v_discr_3576_);
lean_inc(v_resultType_3575_);
lean_dec(v_c_3568_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3654_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3575_, v_a_3572_, v_a_3573_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = 0;
v___x_3584_ = lean_box(0);
v___x_3585_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3586_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3587_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__24));
v___x_3588_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3583_, v___x_3586_, v___x_3585_, v___x_3587_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; lean_object* v_fvarId_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
v_fvarId_3590_ = lean_ctor_get(v_a_3589_, 0);
v___x_3591_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3592_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3593_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__5);
v___x_3594_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7));
v___x_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3595_, 0, v_discr_3576_);
lean_inc(v_fvarId_3590_);
v___x_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3596_, 0, v_fvarId_3590_);
v___x_3597_ = lean_unsigned_to_nat(2u);
v___x_3598_ = lean_mk_empty_array_with_capacity(v___x_3597_);
lean_inc_ref(v___x_3595_);
v___x_3599_ = lean_array_push(v___x_3598_, v___x_3595_);
v___x_3600_ = lean_array_push(v___x_3599_, v___x_3596_);
v___x_3601_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3594_);
lean_ctor_set(v___x_3601_, 1, v___x_3584_);
lean_ctor_set(v___x_3601_, 2, v___x_3600_);
v___x_3602_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3583_, v___x_3591_, v___x_3593_, v___x_3601_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; size_t v_sz_3604_; size_t v___x_3605_; lean_object* v___x_3606_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v_sz_3604_ = lean_array_size(v_alts_3577_);
v___x_3605_ = ((size_t)0ULL);
v___x_3606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3595_, v_sz_3604_, v___x_3605_, v_alts_3577_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3621_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3621_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3621_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v_fvarId_3611_; lean_object* v___x_3613_; 
v_fvarId_3611_ = lean_ctor_get(v_a_3603_, 0);
lean_inc(v_fvarId_3611_);
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 3, v_a_3607_);
lean_ctor_set(v___x_3579_, 2, v_fvarId_3611_);
lean_ctor_set(v___x_3579_, 1, v_a_3582_);
lean_ctor_set(v___x_3579_, 0, v___x_3592_);
v___x_3613_ = v___x_3579_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_a_3582_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_fvarId_3611_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_a_3607_);
v___x_3613_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3614_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v_a_3603_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v_a_3589_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3616_);
v___x_3618_ = v___x_3609_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_a_3603_);
lean_dec(v_a_3589_);
lean_dec(v_a_3582_);
lean_del_object(v___x_3579_);
v_a_3622_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3606_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3606_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref_known(v___x_3595_, 1);
lean_dec(v_a_3589_);
lean_dec(v_a_3582_);
lean_del_object(v___x_3579_);
lean_dec_ref(v_alts_3577_);
v_a_3630_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3602_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3602_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3582_);
lean_del_object(v___x_3579_);
lean_dec_ref(v_alts_3577_);
lean_dec(v_discr_3576_);
v_a_3638_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3588_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3588_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_del_object(v___x_3579_);
lean_dec_ref(v_alts_3577_);
lean_dec(v_discr_3576_);
v_a_3646_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3581_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3581_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_){
_start:
{
lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3672_; lean_object* v___y_3673_; uint8_t v___y_3674_; lean_object* v___y_3679_; lean_object* v___y_3680_; uint8_t v___y_3681_; lean_object* v___y_3686_; lean_object* v___y_3687_; uint8_t v___y_3688_; lean_object* v_decl_3693_; lean_object* v_k_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; 
switch(lean_obj_tag(v_code_3656_))
{
case 0:
{
lean_object* v_decl_3739_; lean_object* v_k_3740_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v_value_3765_; 
v_decl_3739_ = lean_ctor_get(v_code_3656_, 0);
v_k_3740_ = lean_ctor_get(v_code_3656_, 1);
v_value_3765_ = lean_ctor_get(v_decl_3739_, 3);
lean_inc(v_value_3765_);
if (lean_obj_tag(v_value_3765_) == 3)
{
lean_object* v_declName_3766_; 
v_declName_3766_ = lean_ctor_get(v_value_3765_, 0);
lean_inc(v_declName_3766_);
if (lean_obj_tag(v_declName_3766_) == 1)
{
lean_object* v_pre_3767_; 
v_pre_3767_ = lean_ctor_get(v_declName_3766_, 0);
lean_inc(v_pre_3767_);
if (lean_obj_tag(v_pre_3767_) == 1)
{
lean_object* v_pre_3768_; 
v_pre_3768_ = lean_ctor_get(v_pre_3767_, 0);
if (lean_obj_tag(v_pre_3768_) == 0)
{
lean_object* v_type_3769_; lean_object* v_args_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3840_; 
v_type_3769_ = lean_ctor_get(v_decl_3739_, 2);
v_args_3770_ = lean_ctor_get(v_value_3765_, 2);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_value_3765_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; lean_object* v_unused_3842_; 
v_unused_3841_ = lean_ctor_get(v_value_3765_, 1);
lean_dec(v_unused_3841_);
v_unused_3842_ = lean_ctor_get(v_value_3765_, 0);
lean_dec(v_unused_3842_);
v___x_3772_ = v_value_3765_;
v_isShared_3773_ = v_isSharedCheck_3840_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_args_3770_);
lean_dec(v_value_3765_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3840_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v_str_3774_; lean_object* v_str_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_str_3774_ = lean_ctor_get(v_declName_3766_, 1);
lean_inc_ref(v_str_3774_);
lean_dec_ref_known(v_declName_3766_, 2);
v_str_3775_ = lean_ctor_get(v_pre_3767_, 1);
lean_inc_ref(v_str_3775_);
lean_dec_ref_known(v_pre_3767_, 2);
v___x_3776_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_3777_ = lean_string_dec_eq(v_str_3775_, v___x_3776_);
lean_dec_ref(v_str_3775_);
if (v___x_3777_ == 0)
{
lean_dec_ref(v_str_3774_);
lean_del_object(v___x_3772_);
lean_dec_ref(v_args_3770_);
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
v___y_3746_ = v_a_3661_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_3779_ = lean_string_dec_eq(v_str_3774_, v___x_3778_);
lean_dec_ref(v_str_3774_);
if (v___x_3779_ == 0)
{
lean_del_object(v___x_3772_);
lean_dec_ref(v_args_3770_);
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
v___y_3746_ = v_a_3661_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3837_; 
lean_inc_ref(v_type_3769_);
lean_inc_ref(v_k_3740_);
lean_inc_ref(v_decl_3739_);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_code_3656_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; lean_object* v_unused_3839_; 
v_unused_3838_ = lean_ctor_get(v_code_3656_, 1);
lean_dec(v_unused_3838_);
v_unused_3839_ = lean_ctor_get(v_code_3656_, 0);
lean_dec(v_unused_3839_);
v___x_3781_ = v_code_3656_;
v_isShared_3782_ = v_isSharedCheck_3837_;
goto v_resetjp_3780_;
}
else
{
lean_dec(v_code_3656_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3837_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3783_ = lean_array_get_size(v_args_3770_);
v___x_3784_ = lean_unsigned_to_nat(1u);
v___x_3785_ = lean_nat_dec_eq(v___x_3783_, v___x_3784_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_del_object(v___x_3781_);
lean_del_object(v___x_3772_);
lean_dec_ref(v_args_3770_);
lean_dec_ref(v_type_3769_);
lean_dec_ref(v_k_3740_);
lean_dec_ref(v_decl_3739_);
v___x_3786_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3787_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3786_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_3787_;
}
else
{
uint8_t v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3788_ = 0;
v___x_3789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__3));
v___x_3790_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_3791_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3788_, v___x_3789_, v___x_3790_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v_fvarId_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v_fvarId_3793_ = lean_ctor_get(v_a_3792_, 0);
v___x_3794_ = lean_unsigned_to_nat(0u);
v___x_3795_ = lean_array_fget(v_args_3770_, v___x_3794_);
lean_dec_ref(v_args_3770_);
v___x_3796_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3797_ = lean_box(0);
lean_inc(v_fvarId_3793_);
v___x_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_fvarId_3793_);
v___x_3799_ = lean_unsigned_to_nat(2u);
v___x_3800_ = lean_mk_empty_array_with_capacity(v___x_3799_);
v___x_3801_ = lean_array_push(v___x_3800_, v___x_3795_);
v___x_3802_ = lean_array_push(v___x_3801_, v___x_3798_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 2, v___x_3802_);
lean_ctor_set(v___x_3772_, 1, v___x_3797_);
lean_ctor_set(v___x_3772_, 0, v___x_3796_);
v___x_3804_ = v___x_3772_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
lean_object* v___x_3805_; 
v___x_3805_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3788_, v_decl_3739_, v_type_3769_, v___x_3804_, v_a_3659_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3807_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v___x_3807_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3740_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3819_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3819_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 1, v_a_3808_);
lean_ctor_set(v___x_3781_, 0, v_a_3806_);
v___x_3813_ = v___x_3781_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3806_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; lean_object* v___x_3816_; 
v___x_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3814_, 0, v_a_3792_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v___x_3814_);
v___x_3816_ = v___x_3810_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
else
{
lean_dec(v_a_3806_);
lean_dec(v_a_3792_);
lean_del_object(v___x_3781_);
return v___x_3807_;
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_a_3792_);
lean_del_object(v___x_3781_);
lean_dec_ref(v_k_3740_);
v_a_3820_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3805_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3805_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_del_object(v___x_3781_);
lean_del_object(v___x_3772_);
lean_dec_ref(v_args_3770_);
lean_dec_ref(v_type_3769_);
lean_dec_ref(v_k_3740_);
lean_dec_ref(v_decl_3739_);
v_a_3829_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3791_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3791_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
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
lean_dec_ref_known(v_pre_3767_, 2);
lean_dec_ref_known(v_declName_3766_, 2);
lean_dec_ref_known(v_value_3765_, 3);
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
v___y_3746_ = v_a_3661_;
goto v___jp_3741_;
}
}
else
{
lean_dec_ref_known(v_declName_3766_, 2);
lean_dec(v_pre_3767_);
lean_dec_ref_known(v_value_3765_, 3);
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
v___y_3746_ = v_a_3661_;
goto v___jp_3741_;
}
}
else
{
lean_dec(v_declName_3766_);
lean_dec_ref_known(v_value_3765_, 3);
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
v___y_3746_ = v_a_3661_;
goto v___jp_3741_;
}
}
else
{
lean_dec(v_value_3765_);
v___y_3742_ = v_a_3657_;
v___y_3743_ = v_a_3658_;
v___y_3744_ = v_a_3659_;
v___y_3745_ = v_a_3660_;
v___y_3746_ = v_a_3661_;
goto v___jp_3741_;
}
v___jp_3741_:
{
lean_object* v___x_3747_; 
lean_inc_ref(v_decl_3739_);
v___x_3747_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3739_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3749_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_a_3748_);
lean_dec_ref_known(v___x_3747_, 1);
lean_inc_ref(v_k_3740_);
v___x_3749_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3740_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; size_t v___x_3751_; size_t v___x_3752_; uint8_t v___x_3753_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3749_, 1);
v___x_3751_ = lean_ptr_addr(v_k_3740_);
v___x_3752_ = lean_ptr_addr(v_a_3750_);
v___x_3753_ = lean_usize_dec_eq(v___x_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
v___y_3672_ = v_a_3748_;
v___y_3673_ = v_a_3750_;
v___y_3674_ = v___x_3753_;
goto v___jp_3671_;
}
else
{
size_t v___x_3754_; size_t v___x_3755_; uint8_t v___x_3756_; 
v___x_3754_ = lean_ptr_addr(v_decl_3739_);
v___x_3755_ = lean_ptr_addr(v_a_3748_);
v___x_3756_ = lean_usize_dec_eq(v___x_3754_, v___x_3755_);
v___y_3672_ = v_a_3748_;
v___y_3673_ = v_a_3750_;
v___y_3674_ = v___x_3756_;
goto v___jp_3671_;
}
}
else
{
lean_dec(v_a_3748_);
lean_dec_ref_known(v_code_3656_, 2);
return v___x_3749_;
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec_ref_known(v_code_3656_, 2);
v_a_3757_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3747_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3747_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v___x_3762_; 
if (v_isShared_3760_ == 0)
{
v___x_3762_ = v___x_3759_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3757_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_3843_; lean_object* v_args_3844_; size_t v_sz_3845_; size_t v___x_3846_; lean_object* v___x_3847_; 
v_fvarId_3843_ = lean_ctor_get(v_code_3656_, 0);
v_args_3844_ = lean_ctor_get(v_code_3656_, 1);
v_sz_3845_ = lean_array_size(v_args_3844_);
v___x_3846_ = ((size_t)0ULL);
lean_inc_ref(v_args_3844_);
v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3845_, v___x_3846_, v_args_3844_, v_a_3657_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3873_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3850_ = v___x_3847_;
v_isShared_3851_ = v_isSharedCheck_3873_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3847_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3873_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
uint8_t v___y_3853_; uint8_t v___x_3869_; 
v___x_3869_ = l_Lean_instBEqFVarId_beq(v_fvarId_3843_, v_fvarId_3843_);
if (v___x_3869_ == 0)
{
v___y_3853_ = v___x_3869_;
goto v___jp_3852_;
}
else
{
size_t v___x_3870_; size_t v___x_3871_; uint8_t v___x_3872_; 
v___x_3870_ = lean_ptr_addr(v_args_3844_);
v___x_3871_ = lean_ptr_addr(v_a_3848_);
v___x_3872_ = lean_usize_dec_eq(v___x_3870_, v___x_3871_);
v___y_3853_ = v___x_3872_;
goto v___jp_3852_;
}
v___jp_3852_:
{
if (v___y_3853_ == 0)
{
lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3863_; 
lean_inc(v_fvarId_3843_);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_code_3656_);
if (v_isSharedCheck_3863_ == 0)
{
lean_object* v_unused_3864_; lean_object* v_unused_3865_; 
v_unused_3864_ = lean_ctor_get(v_code_3656_, 1);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_code_3656_, 0);
lean_dec(v_unused_3865_);
v___x_3855_ = v_code_3656_;
v_isShared_3856_ = v_isSharedCheck_3863_;
goto v_resetjp_3854_;
}
else
{
lean_dec(v_code_3656_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3863_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 1, v_a_3848_);
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_fvarId_3843_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3848_);
v___x_3858_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
lean_object* v___x_3860_; 
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v___x_3858_);
v___x_3860_ = v___x_3850_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
else
{
lean_object* v___x_3867_; 
lean_dec(v_a_3848_);
if (v_isShared_3851_ == 0)
{
lean_ctor_set(v___x_3850_, 0, v_code_3656_);
v___x_3867_ = v___x_3850_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_code_3656_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref_known(v_code_3656_, 2);
v_a_3874_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3847_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3847_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
case 4:
{
lean_object* v_cases_3882_; lean_object* v_typeName_3883_; lean_object* v_resultType_3884_; lean_object* v_discr_3885_; lean_object* v_alts_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v_cases_3882_ = lean_ctor_get(v_code_3656_, 0);
lean_inc_ref(v_cases_3882_);
v_typeName_3883_ = lean_ctor_get(v_cases_3882_, 0);
v_resultType_3884_ = lean_ctor_get(v_cases_3882_, 1);
v_discr_3885_ = lean_ctor_get(v_cases_3882_, 2);
v_alts_3886_ = lean_ctor_get(v_cases_3882_, 3);
v___x_3887_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__8));
v___x_3888_ = lean_name_eq(v_typeName_3883_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; uint8_t v___x_3890_; 
v___x_3889_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3890_ = lean_name_eq(v_typeName_3883_, v___x_3889_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; uint8_t v___x_3892_; 
v___x_3891_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3892_ = lean_name_eq(v_typeName_3883_, v___x_3891_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; uint8_t v___x_3894_; 
v___x_3893_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__10));
v___x_3894_ = lean_name_eq(v_typeName_3883_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3895_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__12));
v___x_3896_ = lean_name_eq(v_typeName_3883_, v___x_3895_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3897_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__14));
v___x_3898_ = lean_name_eq(v_typeName_3883_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3900_ = lean_name_eq(v_typeName_3883_, v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; uint8_t v___x_3902_; 
v___x_3901_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3902_ = lean_name_eq(v_typeName_3883_, v___x_3901_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; uint8_t v___x_3904_; 
v___x_3903_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3904_ = lean_name_eq(v_typeName_3883_, v___x_3903_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; uint8_t v___x_3906_; 
v___x_3905_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3906_ = lean_name_eq(v_typeName_3883_, v___x_3905_);
if (v___x_3906_ == 0)
{
lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3908_ = lean_name_eq(v_typeName_3883_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3909_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3910_ = lean_name_eq(v_typeName_3883_, v___x_3909_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; uint8_t v___x_3912_; 
v___x_3911_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3912_ = lean_name_eq(v_typeName_3883_, v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3913_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3914_ = lean_name_eq(v_typeName_3883_, v___x_3913_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3915_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__24));
v___x_3916_ = lean_name_eq(v_typeName_3883_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; 
lean_inc(v_typeName_3883_);
v___x_3917_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3883_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
if (lean_obj_tag(v_a_3918_) == 1)
{
lean_object* v_val_3919_; lean_object* v___x_3920_; 
lean_dec_ref_known(v_code_3656_, 1);
v_val_3919_ = lean_ctor_get(v_a_3918_, 0);
lean_inc(v_val_3919_);
lean_dec_ref_known(v_a_3918_, 1);
v___x_3920_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3919_, v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec(v_val_3919_);
return v___x_3920_;
}
else
{
lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_4013_; 
lean_inc_ref(v_alts_3886_);
lean_inc(v_discr_3885_);
lean_inc_ref(v_resultType_3884_);
lean_inc(v_typeName_3883_);
lean_dec(v_a_3918_);
v_isSharedCheck_4013_ = !lean_is_exclusive(v_cases_3882_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; lean_object* v_unused_4015_; lean_object* v_unused_4016_; lean_object* v_unused_4017_; 
v_unused_4014_ = lean_ctor_get(v_cases_3882_, 3);
lean_dec(v_unused_4014_);
v_unused_4015_ = lean_ctor_get(v_cases_3882_, 2);
lean_dec(v_unused_4015_);
v_unused_4016_ = lean_ctor_get(v_cases_3882_, 1);
lean_dec(v_unused_4016_);
v_unused_4017_ = lean_ctor_get(v_cases_3882_, 0);
lean_dec(v_unused_4017_);
v___x_3922_ = v_cases_3882_;
v_isShared_3923_ = v_isSharedCheck_4013_;
goto v_resetjp_3921_;
}
else
{
lean_dec(v_cases_3882_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_4013_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3924_; 
lean_inc_ref(v_resultType_3884_);
v___x_3924_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3884_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_4004_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3927_ = v___x_3924_;
v_isShared_3928_ = v_isSharedCheck_4004_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_4004_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v_env_3930_; lean_object* v___x_3957_; 
v___x_3929_ = lean_st_ref_get(v_a_3661_);
v_env_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc_ref_n(v_env_3930_, 2);
lean_dec(v___x_3929_);
lean_inc(v_typeName_3883_);
v___x_3957_ = l_Lean_Environment_find_x3f(v_env_3930_, v_typeName_3883_, v___x_3916_);
if (lean_obj_tag(v___x_3957_) == 1)
{
lean_object* v_val_3958_; 
v_val_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_val_3958_);
lean_dec_ref_known(v___x_3957_, 1);
if (lean_obj_tag(v_val_3958_) == 5)
{
lean_object* v_val_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4003_; 
v_val_3959_ = lean_ctor_get(v_val_3958_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_val_3958_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3961_ = v_val_3958_;
v_isShared_3962_ = v_isSharedCheck_4003_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_val_3959_);
lean_dec(v_val_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4003_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v_toConstantVal_3963_; lean_object* v_name_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v_toConstantVal_3963_ = lean_ctor_get(v_val_3959_, 0);
lean_inc_ref(v_toConstantVal_3963_);
lean_dec_ref(v_val_3959_);
v_name_3964_ = lean_ctor_get(v_toConstantVal_3963_, 0);
lean_inc(v_name_3964_);
lean_dec_ref(v_toConstantVal_3963_);
v___x_3965_ = l_Lean_mkCasesOnName(v_name_3964_);
lean_inc_ref(v_env_3930_);
v___x_3966_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3930_, v___x_3965_);
if (lean_obj_tag(v___x_3966_) == 0)
{
if (v___x_3916_ == 0)
{
size_t v_sz_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
lean_dec_ref(v_env_3930_);
lean_del_object(v___x_3922_);
v_sz_3967_ = lean_array_size(v_alts_3886_);
v___x_3968_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3886_);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_3967_, v___x_3968_, v_alts_3886_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3994_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3994_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3994_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
uint8_t v___y_3983_; size_t v___x_3988_; size_t v___x_3989_; uint8_t v___x_3990_; 
v___x_3988_ = lean_ptr_addr(v_alts_3886_);
lean_dec_ref(v_alts_3886_);
v___x_3989_ = lean_ptr_addr(v_a_3970_);
v___x_3990_ = lean_usize_dec_eq(v___x_3988_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_dec_ref(v_resultType_3884_);
v___y_3983_ = v___x_3990_;
goto v___jp_3982_;
}
else
{
size_t v___x_3991_; size_t v___x_3992_; uint8_t v___x_3993_; 
v___x_3991_ = lean_ptr_addr(v_resultType_3884_);
lean_dec_ref(v_resultType_3884_);
v___x_3992_ = lean_ptr_addr(v_a_3925_);
v___x_3993_ = lean_usize_dec_eq(v___x_3991_, v___x_3992_);
v___y_3983_ = v___x_3993_;
goto v___jp_3982_;
}
v___jp_3974_:
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
v___x_3975_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3975_, 0, v_typeName_3883_);
lean_ctor_set(v___x_3975_, 1, v_a_3925_);
lean_ctor_set(v___x_3975_, 2, v_discr_3885_);
lean_ctor_set(v___x_3975_, 3, v_a_3970_);
if (v_isShared_3962_ == 0)
{
lean_ctor_set_tag(v___x_3961_, 4);
lean_ctor_set(v___x_3961_, 0, v___x_3975_);
v___x_3977_ = v___x_3961_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
lean_object* v___x_3979_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3977_);
v___x_3979_ = v___x_3972_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
v___jp_3982_:
{
if (v___y_3983_ == 0)
{
lean_del_object(v___x_3927_);
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3974_;
}
else
{
uint8_t v___x_3984_; 
v___x_3984_ = l_Lean_instBEqFVarId_beq(v_discr_3885_, v_discr_3885_);
if (v___x_3984_ == 0)
{
lean_del_object(v___x_3927_);
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3974_;
}
else
{
lean_object* v___x_3986_; 
lean_del_object(v___x_3972_);
lean_dec(v_a_3970_);
lean_del_object(v___x_3961_);
lean_dec(v_a_3925_);
lean_dec(v_discr_3885_);
lean_dec(v_typeName_3883_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v_code_3656_);
v___x_3986_ = v___x_3927_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_code_3656_);
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
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_del_object(v___x_3961_);
lean_del_object(v___x_3927_);
lean_dec(v_a_3925_);
lean_dec_ref(v_alts_3886_);
lean_dec(v_discr_3885_);
lean_dec_ref(v_resultType_3884_);
lean_dec(v_typeName_3883_);
lean_dec_ref_known(v_code_3656_, 1);
v_a_3995_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3969_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3969_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
else
{
lean_del_object(v___x_3961_);
lean_del_object(v___x_3927_);
lean_dec_ref(v_resultType_3884_);
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3931_;
}
}
else
{
lean_dec_ref_known(v___x_3966_, 1);
lean_del_object(v___x_3961_);
lean_del_object(v___x_3927_);
lean_dec_ref(v_resultType_3884_);
lean_dec_ref_known(v_code_3656_, 1);
goto v___jp_3931_;
}
}
}
else
{
lean_dec(v_val_3958_);
lean_dec_ref(v_env_3930_);
lean_del_object(v___x_3927_);
lean_dec(v_a_3925_);
lean_del_object(v___x_3922_);
lean_dec_ref(v_alts_3886_);
lean_dec(v_discr_3885_);
lean_dec_ref(v_resultType_3884_);
lean_dec(v_typeName_3883_);
lean_dec_ref_known(v_code_3656_, 1);
v___y_3664_ = v_a_3657_;
v___y_3665_ = v_a_3658_;
v___y_3666_ = v_a_3659_;
v___y_3667_ = v_a_3660_;
v___y_3668_ = v_a_3661_;
goto v___jp_3663_;
}
}
else
{
lean_dec(v___x_3957_);
lean_dec_ref(v_env_3930_);
lean_del_object(v___x_3927_);
lean_dec(v_a_3925_);
lean_del_object(v___x_3922_);
lean_dec_ref(v_alts_3886_);
lean_dec(v_discr_3885_);
lean_dec_ref(v_resultType_3884_);
lean_dec(v_typeName_3883_);
lean_dec_ref_known(v_code_3656_, 1);
v___y_3664_ = v_a_3657_;
v___y_3665_ = v_a_3658_;
v___y_3666_ = v_a_3659_;
v___y_3667_ = v_a_3660_;
v___y_3668_ = v_a_3661_;
goto v___jp_3663_;
}
v___jp_3931_:
{
size_t v_sz_3932_; size_t v___x_3933_; lean_object* v___x_3934_; 
v_sz_3932_ = lean_array_size(v_alts_3886_);
v___x_3933_ = ((size_t)0ULL);
v___x_3934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_env_3930_, v___x_3916_, v_sz_3932_, v___x_3933_, v_alts_3886_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3948_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3937_ = v___x_3934_;
v_isShared_3938_ = v_isSharedCheck_3948_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3934_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3948_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_3940_ = l_Lean_Name_append(v_typeName_3883_, v___x_3939_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 3, v_a_3935_);
lean_ctor_set(v___x_3922_, 1, v_a_3925_);
lean_ctor_set(v___x_3922_, 0, v___x_3940_);
v___x_3942_ = v___x_3922_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_a_3925_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_discr_3885_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v_a_3935_);
v___x_3942_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 0, v___x_3943_);
v___x_3945_ = v___x_3937_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec(v_a_3925_);
lean_del_object(v___x_3922_);
lean_dec(v_discr_3885_);
lean_dec(v_typeName_3883_);
v_a_3949_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3934_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3934_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
lean_del_object(v___x_3922_);
lean_dec_ref(v_alts_3886_);
lean_dec(v_discr_3885_);
lean_dec_ref(v_resultType_3884_);
lean_dec(v_typeName_3883_);
lean_dec_ref_known(v_code_3656_, 1);
v_a_4005_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3924_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3924_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec_ref(v_cases_3882_);
lean_dec_ref_known(v_code_3656_, 1);
v_a_4018_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_3917_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_3917_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
else
{
lean_object* v___x_4026_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4026_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4026_;
}
}
else
{
lean_object* v___x_4027_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4027_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec_ref(v_cases_3882_);
return v___x_4027_;
}
}
else
{
lean_object* v___x_4028_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4028_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4028_;
}
}
else
{
lean_object* v___x_4029_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4029_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4029_;
}
}
else
{
lean_object* v___x_4030_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4030_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4030_;
}
}
else
{
lean_object* v___x_4031_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4031_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4031_;
}
}
else
{
lean_object* v___x_4032_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4032_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4032_;
}
}
else
{
lean_object* v___x_4033_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4033_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4033_;
}
}
else
{
lean_object* v___x_4034_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4034_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3882_, v___x_3899_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4034_;
}
}
else
{
lean_object* v___x_4035_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4035_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3882_, v___x_3897_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4035_;
}
}
else
{
lean_object* v___x_4036_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4036_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3882_, v___x_3895_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4036_;
}
}
else
{
lean_object* v___x_4037_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4037_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3882_, v___x_3893_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4037_;
}
}
else
{
lean_object* v___x_4038_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4038_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4038_;
}
}
else
{
lean_object* v___x_4039_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4039_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4039_;
}
}
else
{
lean_object* v___x_4040_; 
lean_dec_ref_known(v_code_3656_, 1);
v___x_4040_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_cases_3882_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
return v___x_4040_;
}
}
case 5:
{
lean_object* v___x_4041_; 
v___x_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4041_, 0, v_code_3656_);
return v___x_4041_;
}
case 6:
{
lean_object* v_type_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4066_; 
v_type_4042_ = lean_ctor_get(v_code_3656_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_code_3656_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4044_ = v_code_3656_;
v_isShared_4045_ = v_isSharedCheck_4066_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_type_4042_);
lean_dec(v_code_3656_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4066_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4042_, v_a_3660_, v_a_3661_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4057_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_a_4047_);
v___x_4052_ = v___x_4044_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
lean_object* v___x_4054_; 
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4052_);
v___x_4054_ = v___x_4049_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_del_object(v___x_4044_);
v_a_4058_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4046_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4046_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
default: 
{
lean_object* v_decl_4067_; lean_object* v_k_4068_; 
v_decl_4067_ = lean_ctor_get(v_code_3656_, 0);
v_k_4068_ = lean_ctor_get(v_code_3656_, 1);
lean_inc_ref(v_k_4068_);
lean_inc_ref(v_decl_4067_);
v_decl_3693_ = v_decl_4067_;
v_k_3694_ = v_k_4068_;
v___y_3695_ = v_a_3657_;
v___y_3696_ = v_a_3658_;
v___y_3697_ = v_a_3659_;
v___y_3698_ = v_a_3660_;
v___y_3699_ = v_a_3661_;
goto v___jp_3692_;
}
}
v___jp_3663_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__1, &l_Lean_Compiler_LCNF_Code_toMono___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1);
v___x_3670_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3669_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3670_;
}
v___jp_3671_:
{
if (v___y_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec_ref(v_code_3656_);
v___x_3675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___y_3672_);
lean_ctor_set(v___x_3675_, 1, v___y_3673_);
v___x_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
return v___x_3676_;
}
else
{
lean_object* v___x_3677_; 
lean_dec_ref(v___y_3673_);
lean_dec_ref(v___y_3672_);
v___x_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3677_, 0, v_code_3656_);
return v___x_3677_;
}
}
v___jp_3678_:
{
if (v___y_3681_ == 0)
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_dec_ref(v_code_3656_);
v___x_3682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___y_3679_);
lean_ctor_set(v___x_3682_, 1, v___y_3680_);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
else
{
lean_object* v___x_3684_; 
lean_dec_ref(v___y_3680_);
lean_dec_ref(v___y_3679_);
v___x_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3684_, 0, v_code_3656_);
return v___x_3684_;
}
}
v___jp_3685_:
{
if (v___y_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
lean_dec_ref(v_code_3656_);
v___x_3689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___y_3686_);
lean_ctor_set(v___x_3689_, 1, v___y_3687_);
v___x_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
else
{
lean_object* v___x_3691_; 
lean_dec_ref(v___y_3687_);
lean_dec_ref(v___y_3686_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v_code_3656_);
return v___x_3691_;
}
}
v___jp_3692_:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3693_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3702_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref_known(v___x_3700_, 1);
v___x_3702_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
if (lean_obj_tag(v___x_3702_) == 0)
{
switch(lean_obj_tag(v_code_3656_))
{
case 1:
{
lean_object* v_a_3703_; lean_object* v_decl_3704_; lean_object* v_k_3705_; size_t v___x_3706_; size_t v___x_3707_; uint8_t v___x_3708_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3703_);
lean_dec_ref_known(v___x_3702_, 1);
v_decl_3704_ = lean_ctor_get(v_code_3656_, 0);
v_k_3705_ = lean_ctor_get(v_code_3656_, 1);
v___x_3706_ = lean_ptr_addr(v_k_3705_);
v___x_3707_ = lean_ptr_addr(v_a_3703_);
v___x_3708_ = lean_usize_dec_eq(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
v___y_3679_ = v_a_3701_;
v___y_3680_ = v_a_3703_;
v___y_3681_ = v___x_3708_;
goto v___jp_3678_;
}
else
{
size_t v___x_3709_; size_t v___x_3710_; uint8_t v___x_3711_; 
v___x_3709_ = lean_ptr_addr(v_decl_3704_);
v___x_3710_ = lean_ptr_addr(v_a_3701_);
v___x_3711_ = lean_usize_dec_eq(v___x_3709_, v___x_3710_);
v___y_3679_ = v_a_3701_;
v___y_3680_ = v_a_3703_;
v___y_3681_ = v___x_3711_;
goto v___jp_3678_;
}
}
case 2:
{
lean_object* v_a_3712_; lean_object* v_decl_3713_; lean_object* v_k_3714_; size_t v___x_3715_; size_t v___x_3716_; uint8_t v___x_3717_; 
v_a_3712_ = lean_ctor_get(v___x_3702_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3702_, 1);
v_decl_3713_ = lean_ctor_get(v_code_3656_, 0);
v_k_3714_ = lean_ctor_get(v_code_3656_, 1);
v___x_3715_ = lean_ptr_addr(v_k_3714_);
v___x_3716_ = lean_ptr_addr(v_a_3712_);
v___x_3717_ = lean_usize_dec_eq(v___x_3715_, v___x_3716_);
if (v___x_3717_ == 0)
{
v___y_3686_ = v_a_3701_;
v___y_3687_ = v_a_3712_;
v___y_3688_ = v___x_3717_;
goto v___jp_3685_;
}
else
{
size_t v___x_3718_; size_t v___x_3719_; uint8_t v___x_3720_; 
v___x_3718_ = lean_ptr_addr(v_decl_3713_);
v___x_3719_ = lean_ptr_addr(v_a_3701_);
v___x_3720_ = lean_usize_dec_eq(v___x_3718_, v___x_3719_);
v___y_3686_ = v_a_3701_;
v___y_3687_ = v_a_3712_;
v___y_3688_ = v___x_3720_;
goto v___jp_3685_;
}
}
default: 
{
lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v_a_3701_);
lean_dec_ref(v_code_3656_);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v___x_3702_, 0);
lean_dec(v_unused_3730_);
v___x_3722_ = v___x_3702_;
v_isShared_3723_ = v_isSharedCheck_3729_;
goto v_resetjp_3721_;
}
else
{
lean_dec(v___x_3702_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3729_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3724_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3725_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3724_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3725_);
v___x_3727_ = v___x_3722_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
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
}
else
{
lean_dec(v_a_3701_);
lean_dec_ref(v_code_3656_);
return v___x_3702_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec_ref(v_k_3694_);
lean_dec_ref(v_code_3656_);
v_a_3731_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3700_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3700_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(size_t v_sz_4069_, size_t v_i_4070_, lean_object* v_bs_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
uint8_t v___x_4078_; 
v___x_4078_ = lean_usize_dec_lt(v_i_4070_, v_sz_4069_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v_bs_4071_);
return v___x_4079_;
}
else
{
lean_object* v_v_4080_; lean_object* v___x_4081_; lean_object* v_bs_x27_4082_; lean_object* v_a_4084_; 
v_v_4080_ = lean_array_uget(v_bs_4071_, v_i_4070_);
v___x_4081_ = lean_unsigned_to_nat(0u);
v_bs_x27_4082_ = lean_array_uset(v_bs_4071_, v_i_4070_, v___x_4081_);
if (lean_obj_tag(v_v_4080_) == 0)
{
lean_object* v_ctorName_4089_; lean_object* v_params_4090_; lean_object* v_code_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4125_; 
v_ctorName_4089_ = lean_ctor_get(v_v_4080_, 0);
v_params_4090_ = lean_ctor_get(v_v_4080_, 1);
v_code_4091_ = lean_ctor_get(v_v_4080_, 2);
v_isSharedCheck_4125_ = !lean_is_exclusive(v_v_4080_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4093_ = v_v_4080_;
v_isShared_4094_ = v_isSharedCheck_4125_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_code_4091_);
lean_inc(v_params_4090_);
lean_inc(v_ctorName_4089_);
lean_dec(v_v_4080_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4125_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
uint8_t v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = 0;
v___x_4096_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_4095_, v_params_4090_, v___y_4074_);
lean_dec_ref(v_params_4090_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___y_4098_; lean_object* v___x_4113_; uint8_t v___x_4114_; 
lean_dec_ref_known(v___x_4096_, 1);
v___x_4113_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_4114_ = lean_name_eq(v_ctorName_4089_, v___x_4113_);
lean_dec(v_ctorName_4089_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; 
v___x_4115_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___y_4098_ = v___x_4115_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4116_; 
v___x_4116_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___y_4098_ = v___x_4116_;
goto v___jp_4097_;
}
v___jp_4097_:
{
lean_object* v___x_4099_; 
v___x_4099_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4091_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; lean_object* v___x_4103_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4099_, 1);
v___x_4101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___closed__0));
lean_inc(v___y_4098_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set(v___x_4093_, 2, v_a_4100_);
lean_ctor_set(v___x_4093_, 1, v___x_4101_);
lean_ctor_set(v___x_4093_, 0, v___y_4098_);
v___x_4103_ = v___x_4093_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v___y_4098_);
lean_ctor_set(v_reuseFailAlloc_4104_, 1, v___x_4101_);
lean_ctor_set(v_reuseFailAlloc_4104_, 2, v_a_4100_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
v_a_4084_ = v___x_4103_;
goto v___jp_4083_;
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_del_object(v___x_4093_);
lean_dec_ref(v_bs_x27_4082_);
v_a_4105_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4099_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4099_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_del_object(v___x_4093_);
lean_dec_ref(v_code_4091_);
lean_dec(v_ctorName_4089_);
lean_dec_ref(v_bs_x27_4082_);
v_a_4117_ = lean_ctor_get(v___x_4096_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4096_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4096_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4096_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
else
{
lean_object* v_code_4126_; lean_object* v___x_4127_; 
v_code_4126_ = lean_ctor_get(v_v_4080_, 0);
lean_inc_ref(v_code_4126_);
v___x_4127_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4126_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_4080_, v_a_4128_);
v_a_4084_ = v___x_4129_;
goto v___jp_4083_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref_known(v_v_4080_, 1);
lean_dec_ref(v_bs_x27_4082_);
v_a_4130_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4127_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4127_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
v___jp_4083_:
{
size_t v___x_4085_; size_t v___x_4086_; lean_object* v___x_4087_; 
v___x_4085_ = ((size_t)1ULL);
v___x_4086_ = lean_usize_add(v_i_4070_, v___x_4085_);
v___x_4087_ = lean_array_uset(v_bs_x27_4082_, v_i_4070_, v_a_4084_);
v_i_4070_ = v___x_4086_;
v_bs_4071_ = v___x_4087_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object* v_c_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v_resultType_4145_; lean_object* v_discr_4146_; lean_object* v_alts_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4185_; 
v_resultType_4145_ = lean_ctor_get(v_c_4138_, 1);
v_discr_4146_ = lean_ctor_get(v_c_4138_, 2);
v_alts_4147_ = lean_ctor_get(v_c_4138_, 3);
v_isSharedCheck_4185_ = !lean_is_exclusive(v_c_4138_);
if (v_isSharedCheck_4185_ == 0)
{
lean_object* v_unused_4186_; 
v_unused_4186_ = lean_ctor_get(v_c_4138_, 0);
lean_dec(v_unused_4186_);
v___x_4149_ = v_c_4138_;
v_isShared_4150_ = v_isSharedCheck_4185_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_alts_4147_);
lean_inc(v_discr_4146_);
lean_inc(v_resultType_4145_);
lean_dec(v_c_4138_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4185_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_4145_, v_a_4142_, v_a_4143_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; size_t v_sz_4153_; size_t v___x_4154_; lean_object* v___x_4155_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v_sz_4153_ = lean_array_size(v_alts_4147_);
v___x_4154_ = ((size_t)0ULL);
v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(v_sz_4153_, v___x_4154_, v_alts_4147_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4168_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4168_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4168_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4160_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 3, v_a_4156_);
lean_ctor_set(v___x_4149_, 1, v_a_4152_);
lean_ctor_set(v___x_4149_, 0, v___x_4160_);
v___x_4162_ = v___x_4149_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_a_4152_);
lean_ctor_set(v_reuseFailAlloc_4167_, 2, v_discr_4146_);
lean_ctor_set(v_reuseFailAlloc_4167_, 3, v_a_4156_);
v___x_4162_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4163_; lean_object* v___x_4165_; 
v___x_4163_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v___x_4163_);
v___x_4165_ = v___x_4158_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4163_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v_a_4152_);
lean_del_object(v___x_4149_);
lean_dec(v_discr_4146_);
v_a_4169_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4155_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4155_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_del_object(v___x_4149_);
lean_dec_ref(v_alts_4147_);
lean_dec(v_discr_4146_);
v_a_4177_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4151_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4151_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object* v_c_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
lean_dec_ref(v_a_4189_);
lean_dec(v_a_4188_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
lean_dec(v_a_4198_);
lean_dec_ref(v_a_4197_);
lean_dec(v_a_4196_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_4203_, lean_object* v_i_4204_, lean_object* v_bs_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
size_t v_sz_boxed_4212_; size_t v_i_boxed_4213_; lean_object* v_res_4214_; 
v_sz_boxed_4212_ = lean_unbox_usize(v_sz_4203_);
lean_dec(v_sz_4203_);
v_i_boxed_4213_ = lean_unbox_usize(v_i_4204_);
lean_dec(v_i_4204_);
v_res_4214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_4212_, v_i_boxed_4213_, v_bs_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
return v_res_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22___boxed(lean_object* v_sz_4215_, lean_object* v_i_4216_, lean_object* v_bs_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
size_t v_sz_boxed_4224_; size_t v_i_boxed_4225_; lean_object* v_res_4226_; 
v_sz_boxed_4224_ = lean_unbox_usize(v_sz_4215_);
lean_dec(v_sz_4215_);
v_i_boxed_4225_ = lean_unbox_usize(v_i_4216_);
lean_dec(v_i_4216_);
v_res_4226_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__22(v_sz_boxed_4224_, v_i_boxed_4225_, v_bs_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec(v_a_4230_);
lean_dec_ref(v_a_4229_);
lean_dec(v_a_4228_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_4235_, lean_object* v_uintName_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4235_, v_uintName_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_);
lean_dec(v_a_4241_);
lean_dec_ref(v_a_4240_);
lean_dec(v_a_4239_);
lean_dec_ref(v_a_4238_);
lean_dec(v_a_4237_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
lean_dec(v_a_4253_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_);
lean_dec(v_a_4265_);
lean_dec_ref(v_a_4264_);
lean_dec(v_a_4263_);
lean_dec_ref(v_a_4262_);
lean_dec(v_a_4261_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_);
lean_dec(v_a_4273_);
lean_dec_ref(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec_ref(v_a_4270_);
lean_dec(v_a_4269_);
return v_res_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v_sz_4286_, lean_object* v_i_4287_, lean_object* v_bs_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
uint8_t v___x_47244__boxed_4295_; size_t v_sz_boxed_4296_; size_t v_i_boxed_4297_; lean_object* v_res_4298_; 
v___x_47244__boxed_4295_ = lean_unbox(v___x_4285_);
v_sz_boxed_4296_ = lean_unbox_usize(v_sz_4286_);
lean_dec(v_sz_4286_);
v_i_boxed_4297_ = lean_unbox_usize(v_i_4287_);
lean_dec(v_i_4287_);
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_4284_, v___x_47244__boxed_4295_, v_sz_boxed_4296_, v_i_boxed_4297_, v_bs_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4308_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_4323_, lean_object* v_c_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_4323_, v_c_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_info_4323_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_4332_, lean_object* v_sz_4333_, lean_object* v_i_4334_, lean_object* v_bs_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
size_t v_sz_boxed_4342_; size_t v_i_boxed_4343_; lean_object* v_res_4344_; 
v_sz_boxed_4342_ = lean_unbox_usize(v_sz_4333_);
lean_dec(v_sz_4333_);
v_i_boxed_4343_ = lean_unbox_usize(v_i_4334_);
lean_dec(v_i_4334_);
v_res_4344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_4332_, v_sz_boxed_4342_, v_i_boxed_4343_, v_bs_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_);
lean_dec(v_a_4350_);
lean_dec_ref(v_a_4349_);
lean_dec(v_a_4348_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_c_4345_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_4353_, lean_object* v_sz_4354_, lean_object* v_i_4355_, lean_object* v_bs_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
size_t v_sz_boxed_4363_; size_t v_i_boxed_4364_; lean_object* v_res_4365_; 
v_sz_boxed_4363_ = lean_unbox_usize(v_sz_4354_);
lean_dec(v_sz_4354_);
v_i_boxed_4364_ = lean_unbox_usize(v_i_4355_);
lean_dec(v_i_4355_);
v_res_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_4353_, v_sz_boxed_4363_, v_i_boxed_4364_, v_bs_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4374_, lean_object* v_x_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v___x_4382_; 
v___x_4382_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4374_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
return v___x_4382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4383_, lean_object* v_x_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4383_, v_x_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4392_, lean_object* v_x_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4392_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4401_, lean_object* v_x_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_){
_start:
{
lean_object* v_res_4409_; 
v_res_4409_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4401_, v_x_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
lean_dec(v_a_4407_);
lean_dec_ref(v_a_4406_);
lean_dec(v_a_4405_);
lean_dec_ref(v_a_4404_);
lean_dec(v_a_4403_);
lean_dec_ref(v_c_4401_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4410_, lean_object* v_x_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_){
_start:
{
lean_object* v___x_4418_; 
v___x_4418_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4410_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4419_, lean_object* v_x_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4419_, v_x_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4428_, lean_object* v_x_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v___x_4436_; 
v___x_4436_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4428_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_);
return v___x_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4437_, lean_object* v_x_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4437_, v_x_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
lean_dec(v_a_4441_);
lean_dec_ref(v_a_4440_);
lean_dec(v_a_4439_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4446_, lean_object* v_x_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v___x_4454_; 
v___x_4454_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4446_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
return v___x_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4455_, lean_object* v_x_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4455_, v_x_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4464_, lean_object* v_x_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v___x_4472_; 
v___x_4472_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4464_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4473_, lean_object* v_x_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4473_, v_x_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4482_, lean_object* v_x_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4482_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4491_, lean_object* v_x_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v_res_4499_; 
v_res_4499_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4491_, v_x_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
lean_dec(v_a_4493_);
return v_res_4499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4500_, lean_object* v_x_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4500_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4509_, lean_object* v_x_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4509_, v_x_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4518_, lean_object* v_uintName_4519_, lean_object* v_x_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v___x_4527_; 
v___x_4527_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4518_, v_uintName_4519_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4528_, lean_object* v_uintName_4529_, lean_object* v_x_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_){
_start:
{
lean_object* v_res_4537_; 
v_res_4537_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4528_, v_uintName_4529_, v_x_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec_ref(v_a_4532_);
lean_dec(v_a_4531_);
return v_res_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4538_, lean_object* v_x_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4538_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4547_, lean_object* v_x_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4547_, v_x_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4556_, lean_object* v_x_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_){
_start:
{
lean_object* v___x_4564_; 
v___x_4564_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4556_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
return v___x_4564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4565_, lean_object* v_x_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_){
_start:
{
lean_object* v_res_4573_; 
v_res_4573_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4565_, v_x_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
return v_res_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object* v_c_4574_, lean_object* v_x_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4574_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
return v___x_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___boxed(lean_object* v_c_4583_, lean_object* v_x_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v_res_4591_; 
v_res_4591_ = l_Lean_Compiler_LCNF_decToMono(v_c_4583_, v_x_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4592_, size_t v_i_4593_, lean_object* v_bs_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4592_, v_i_4593_, v_bs_4594_, v___y_4595_, v___y_4597_, v___y_4598_, v___y_4599_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4602_, lean_object* v_i_4603_, lean_object* v_bs_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
size_t v_sz_boxed_4611_; size_t v_i_boxed_4612_; lean_object* v_res_4613_; 
v_sz_boxed_4611_ = lean_unbox_usize(v_sz_4602_);
lean_dec(v_sz_4602_);
v_i_boxed_4612_ = lean_unbox_usize(v_i_4603_);
lean_dec(v_i_4603_);
v_res_4613_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4611_, v_i_boxed_4612_, v_bs_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
return v_res_4613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4614_, lean_object* v_v_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
if (lean_obj_tag(v_v_4615_) == 0)
{
lean_object* v_code_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4646_; 
v_code_4622_ = lean_ctor_get(v_v_4615_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_v_4615_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4624_ = v_v_4615_;
v_isShared_4625_ = v_isSharedCheck_4646_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_code_4622_);
lean_dec(v_v_4615_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4646_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; 
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc(v___y_4616_);
v___x_4626_ = lean_apply_7(v_f_4614_, v_code_4622_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, lean_box(0));
if (lean_obj_tag(v___x_4626_) == 0)
{
lean_object* v_a_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4637_; 
v_a_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4637_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_a_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4637_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v_a_4627_);
v___x_4632_ = v___x_4624_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4627_);
v___x_4632_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4634_; 
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 0, v___x_4632_);
v___x_4634_ = v___x_4629_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4635_; 
v_reuseFailAlloc_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4635_, 0, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4635_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
return v___x_4634_;
}
}
}
}
else
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4645_; 
lean_del_object(v___x_4624_);
v_a_4638_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4640_ = v___x_4626_;
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4626_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4645_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4643_; 
if (v_isShared_4641_ == 0)
{
v___x_4643_ = v___x_4640_;
goto v_reusejp_4642_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4638_);
v___x_4643_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4642_;
}
v_reusejp_4642_:
{
return v___x_4643_;
}
}
}
}
}
else
{
lean_object* v___x_4647_; 
lean_dec_ref(v_f_4614_);
v___x_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4647_, 0, v_v_4615_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4648_, lean_object* v_v_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4648_, v_v_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4657_, lean_object* v_f_4658_, lean_object* v_v_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_){
_start:
{
lean_object* v___x_4666_; 
v___x_4666_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4658_, v_v_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4667_, lean_object* v_f_4668_, lean_object* v_v_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
uint8_t v_pu_boxed_4676_; lean_object* v_res_4677_; 
v_pu_boxed_4676_ = lean_unbox(v_pu_4667_);
v_res_4677_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4676_, v_f_4668_, v_v_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
lean_dec(v___y_4674_);
lean_dec_ref(v___y_4673_);
lean_dec(v___y_4672_);
lean_dec_ref(v___y_4671_);
lean_dec(v___y_4670_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_){
_start:
{
lean_object* v_toSignature_4686_; lean_object* v_value_4687_; uint8_t v_recursive_4688_; lean_object* v_inlineAttr_x3f_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4759_; 
v_toSignature_4686_ = lean_ctor_get(v_decl_4679_, 0);
v_value_4687_ = lean_ctor_get(v_decl_4679_, 1);
v_recursive_4688_ = lean_ctor_get_uint8(v_decl_4679_, sizeof(void*)*3);
v_inlineAttr_x3f_4689_ = lean_ctor_get(v_decl_4679_, 2);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_decl_4679_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4691_ = v_decl_4679_;
v_isShared_4692_ = v_isSharedCheck_4759_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_inlineAttr_x3f_4689_);
lean_inc(v_value_4687_);
lean_inc(v_toSignature_4686_);
lean_dec(v_decl_4679_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4759_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v_name_4693_; lean_object* v_type_4694_; lean_object* v_params_4695_; uint8_t v_safe_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4757_; 
v_name_4693_ = lean_ctor_get(v_toSignature_4686_, 0);
v_type_4694_ = lean_ctor_get(v_toSignature_4686_, 2);
v_params_4695_ = lean_ctor_get(v_toSignature_4686_, 3);
v_safe_4696_ = lean_ctor_get_uint8(v_toSignature_4686_, sizeof(void*)*4);
v_isSharedCheck_4757_ = !lean_is_exclusive(v_toSignature_4686_);
if (v_isSharedCheck_4757_ == 0)
{
lean_object* v_unused_4758_; 
v_unused_4758_ = lean_ctor_get(v_toSignature_4686_, 1);
lean_dec(v_unused_4758_);
v___x_4698_ = v_toSignature_4686_;
v_isShared_4699_ = v_isSharedCheck_4757_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_params_4695_);
lean_inc(v_type_4694_);
lean_inc(v_name_4693_);
lean_dec(v_toSignature_4686_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4757_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4694_, v_a_4683_, v_a_4684_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; size_t v_sz_4702_; size_t v___x_4703_; lean_object* v___x_4704_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v_sz_4702_ = lean_array_size(v_params_4695_);
v___x_4703_ = ((size_t)0ULL);
v___x_4704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4702_, v___x_4703_, v_params_4695_, v_a_4680_, v_a_4682_, v_a_4683_, v_a_4684_);
if (lean_obj_tag(v___x_4704_) == 0)
{
lean_object* v_a_4705_; lean_object* v___f_4706_; lean_object* v___x_4707_; 
v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc(v_a_4705_);
lean_dec_ref_known(v___x_4704_, 1);
v___f_4706_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4707_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4706_, v_value_4687_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4709_; lean_object* v___x_4711_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___x_4707_, 1);
v___x_4709_ = lean_box(0);
if (v_isShared_4699_ == 0)
{
lean_ctor_set(v___x_4698_, 3, v_a_4705_);
lean_ctor_set(v___x_4698_, 2, v_a_4701_);
lean_ctor_set(v___x_4698_, 1, v___x_4709_);
v___x_4711_ = v___x_4698_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_name_4693_);
lean_ctor_set(v_reuseFailAlloc_4732_, 1, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4732_, 2, v_a_4701_);
lean_ctor_set(v_reuseFailAlloc_4732_, 3, v_a_4705_);
lean_ctor_set_uint8(v_reuseFailAlloc_4732_, sizeof(void*)*4, v_safe_4696_);
v___x_4711_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
lean_object* v___x_4713_; 
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 1, v_a_4708_);
lean_ctor_set(v___x_4691_, 0, v___x_4711_);
v___x_4713_ = v___x_4691_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4731_; 
v_reuseFailAlloc_4731_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4731_, 0, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4731_, 1, v_a_4708_);
lean_ctor_set(v_reuseFailAlloc_4731_, 2, v_inlineAttr_x3f_4689_);
lean_ctor_set_uint8(v_reuseFailAlloc_4731_, sizeof(void*)*3, v_recursive_4688_);
v___x_4713_ = v_reuseFailAlloc_4731_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
lean_object* v___x_4714_; 
lean_inc_ref(v___x_4713_);
v___x_4714_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4713_, v_a_4684_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4721_; 
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4721_ == 0)
{
lean_object* v_unused_4722_; 
v_unused_4722_ = lean_ctor_get(v___x_4714_, 0);
lean_dec(v_unused_4722_);
v___x_4716_ = v___x_4714_;
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
else
{
lean_dec(v___x_4714_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4721_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4719_; 
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 0, v___x_4713_);
v___x_4719_ = v___x_4716_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4713_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
else
{
lean_object* v_a_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4730_; 
lean_dec_ref(v___x_4713_);
v_a_4723_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4725_ = v___x_4714_;
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_a_4723_);
lean_dec(v___x_4714_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4728_; 
if (v_isShared_4726_ == 0)
{
v___x_4728_ = v___x_4725_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4723_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
}
}
}
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec(v_a_4705_);
lean_dec(v_a_4701_);
lean_del_object(v___x_4698_);
lean_dec(v_name_4693_);
lean_del_object(v___x_4691_);
lean_dec(v_inlineAttr_x3f_4689_);
v_a_4733_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4707_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4707_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec(v_a_4701_);
lean_del_object(v___x_4698_);
lean_dec(v_name_4693_);
lean_del_object(v___x_4691_);
lean_dec(v_inlineAttr_x3f_4689_);
lean_dec_ref(v_value_4687_);
v_a_4741_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4704_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4704_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_del_object(v___x_4698_);
lean_dec_ref(v_params_4695_);
lean_dec(v_name_4693_);
lean_del_object(v___x_4691_);
lean_dec(v_inlineAttr_x3f_4689_);
lean_dec_ref(v_value_4687_);
v_a_4749_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4700_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4700_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4760_, v_a_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec(v_a_4761_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4774_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4775_ = lean_st_mk_ref(v___x_4774_);
v___x_4776_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4768_, v___x_4775_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4785_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4779_ = v___x_4776_;
v_isShared_4780_ = v_isSharedCheck_4785_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4776_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4785_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4781_; lean_object* v___x_4783_; 
v___x_4781_ = lean_st_ref_get(v___x_4775_);
lean_dec(v___x_4775_);
lean_dec(v___x_4781_);
if (v_isShared_4780_ == 0)
{
v___x_4783_ = v___x_4779_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4777_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
else
{
lean_dec(v___x_4775_);
return v___x_4776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
lean_dec(v_a_4790_);
lean_dec_ref(v_a_4789_);
lean_dec(v_a_4788_);
lean_dec_ref(v_a_4787_);
return v_res_4792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4793_, size_t v_i_4794_, lean_object* v_bs_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
uint8_t v___x_4801_; 
v___x_4801_ = lean_usize_dec_lt(v_i_4794_, v_sz_4793_);
if (v___x_4801_ == 0)
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_bs_4795_);
return v___x_4802_;
}
else
{
lean_object* v_v_4803_; lean_object* v___x_4804_; 
v_v_4803_ = lean_array_uget_borrowed(v_bs_4795_, v_i_4794_);
lean_inc(v_v_4803_);
v___x_4804_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4803_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; lean_object* v___x_4806_; lean_object* v_bs_x27_4807_; size_t v___x_4808_; size_t v___x_4809_; lean_object* v___x_4810_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v___x_4806_ = lean_unsigned_to_nat(0u);
v_bs_x27_4807_ = lean_array_uset(v_bs_4795_, v_i_4794_, v___x_4806_);
v___x_4808_ = ((size_t)1ULL);
v___x_4809_ = lean_usize_add(v_i_4794_, v___x_4808_);
v___x_4810_ = lean_array_uset(v_bs_x27_4807_, v_i_4794_, v_a_4805_);
v_i_4794_ = v___x_4809_;
v_bs_4795_ = v___x_4810_;
goto _start;
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_dec_ref(v_bs_4795_);
v_a_4812_ = lean_ctor_get(v___x_4804_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4804_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4804_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4804_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4820_, lean_object* v_i_4821_, lean_object* v_bs_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
size_t v_sz_boxed_4828_; size_t v_i_boxed_4829_; lean_object* v_res_4830_; 
v_sz_boxed_4828_ = lean_unbox_usize(v_sz_4820_);
lean_dec(v_sz_4820_);
v_i_boxed_4829_ = lean_unbox_usize(v_i_4821_);
lean_dec(v_i_4821_);
v_res_4830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4828_, v_i_boxed_4829_, v_bs_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
return v_res_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
size_t v_sz_4837_; size_t v___x_4838_; lean_object* v___x_4839_; 
v_sz_4837_ = lean_array_size(v_x_4831_);
v___x_4838_ = ((size_t)0ULL);
v___x_4839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4837_, v___x_4838_, v_x_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
return v___x_4839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
lean_dec(v___y_4844_);
lean_dec_ref(v___y_4843_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4929_; uint8_t v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4929_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4930_ = 1;
v___x_4931_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4932_ = l_Lean_registerTraceClass(v___x_4929_, v___x_4930_, v___x_4931_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4934_;
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
