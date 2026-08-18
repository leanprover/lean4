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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default(uint8_t);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_argToMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqFVarId_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_argToMono___redArg___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_argToMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableFVarId_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_argToMono___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = l_Lean_instBEqFVarId_beq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
v___x_62_ = l_Lean_instHashableFVarId_hash(v_query_59_);
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___x_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___x_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_usize_to_nat(v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg(lean_object* v_b_80_, lean_object* v_acc_81_, lean_object* v_i_82_){
_start:
{
lean_object* v___y_84_; lean_object* v_keyArray_92_; lean_object* v_valueArray_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_keyArray_92_ = lean_ctor_get(v_b_80_, 1);
v_valueArray_93_ = lean_ctor_get(v_b_80_, 2);
v___x_94_ = lean_array_get_size(v_keyArray_92_);
v___x_95_ = lean_nat_dec_lt(v_i_82_, v___x_94_);
if (v___x_95_ == 0)
{
lean_dec(v_i_82_);
return v_acc_81_;
}
else
{
lean_object* v___x_96_; uint8_t v_isSome_97_; 
v___x_96_ = lean_array_fget_borrowed(v_keyArray_92_, v_i_82_);
v_isSome_97_ = lean_noption_is_some(v___x_96_);
if (v_isSome_97_ == 0)
{
goto v___jp_88_;
}
else
{
lean_object* v___x_98_; uint8_t v_isSome_99_; 
v___x_98_ = lean_array_fget_borrowed(v_valueArray_93_, v_i_82_);
v_isSome_99_ = lean_noption_is_some(v___x_98_);
if (v_isSome_99_ == 0)
{
goto v___jp_88_;
}
else
{
lean_object* v_val_100_; lean_object* v_val_101_; lean_object* v_i_103_; lean_object* v___x_108_; 
lean_inc(v___x_96_);
v_val_100_ = lean_noption_get(v___x_96_);
lean_inc(v___x_98_);
v_val_101_ = lean_noption_get(v___x_98_);
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_acc_81_, v_val_100_);
switch(lean_obj_tag(v___x_108_))
{
case 0:
{
lean_object* v_index_109_; lean_object* v_size_110_; lean_object* v___x_111_; 
v_index_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_index_109_);
lean_dec_ref_known(v___x_108_, 3);
v_size_110_ = lean_ctor_get(v_acc_81_, 0);
lean_inc(v_size_110_);
v___x_111_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_81_, v_size_110_, v_index_109_, v_val_100_, v_val_101_);
lean_dec(v_index_109_);
v___y_84_ = v___x_111_;
goto v___jp_83_;
}
case 1:
{
lean_object* v_index_112_; 
v_index_112_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_index_112_);
lean_dec_ref_known(v___x_108_, 1);
v_i_103_ = v_index_112_;
goto v___jp_102_;
}
default: 
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_81_, v___x_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_index_115_; 
v_index_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_index_115_);
lean_dec_ref_known(v___x_114_, 1);
v_i_103_ = v_index_115_;
goto v___jp_102_;
}
else
{
lean_dec(v_val_101_);
lean_dec(v_val_100_);
v___y_84_ = v_acc_81_;
goto v___jp_83_;
}
}
}
v___jp_102_:
{
lean_object* v_size_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_size_104_ = lean_ctor_get(v_acc_81_, 0);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_size_104_, v___x_105_);
v___x_107_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_81_, v___x_106_, v_i_103_, v_val_100_, v_val_101_);
lean_dec(v_i_103_);
v___y_84_ = v___x_107_;
goto v___jp_83_;
}
}
}
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_i_82_, v___x_85_);
lean_dec(v_i_82_);
v_acc_81_ = v___y_84_;
v_i_82_ = v___x_86_;
goto _start;
}
v___jp_88_:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = lean_nat_add(v_i_82_, v___x_89_);
lean_dec(v_i_82_);
v_i_82_ = v___x_90_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_116_, lean_object* v_acc_117_, lean_object* v_i_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg(v_b_116_, v_acc_117_, v_i_118_);
lean_dec_ref(v_b_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg(lean_object* v_init_120_, lean_object* v_b_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg(v_b_121_, v_init_120_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg___boxed(lean_object* v_init_124_, lean_object* v_b_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg(v_init_124_, v_b_125_);
lean_dec_ref(v_b_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(lean_object* v_m_127_){
_start:
{
lean_object* v_keyArray_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_cellCount_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_target_135_; lean_object* v___x_136_; 
v_keyArray_128_ = lean_ctor_get(v_m_127_, 1);
v___x_129_ = lean_array_get_size(v_keyArray_128_);
v___x_130_ = lean_unsigned_to_nat(2u);
v_cellCount_131_ = lean_nat_mul(v___x_129_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_131_);
v___x_133_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_131_);
v___x_134_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_131_);
v_target_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_135_, 0, v___x_132_);
lean_ctor_set(v_target_135_, 1, v___x_133_);
lean_ctor_set(v_target_135_, 2, v___x_134_);
v___x_136_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg(v_target_135_, v_m_127_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg___boxed(lean_object* v_m_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(v_m_137_);
lean_dec_ref(v_m_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object* v_param_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_fvarId_145_; lean_object* v_type_146_; lean_object* v___y_148_; lean_object* v___y_149_; lean_object* v___y_150_; uint8_t v___x_163_; 
v_fvarId_145_ = lean_ctor_get(v_param_139_, 0);
v_type_146_ = lean_ctor_get(v_param_139_, 2);
lean_inc_ref(v_type_146_);
v___x_163_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_146_);
if (v___x_163_ == 0)
{
v___y_148_ = v_a_141_;
v___y_149_ = v_a_142_;
v___y_150_ = v_a_143_;
goto v___jp_147_;
}
else
{
lean_object* v___x_164_; lean_object* v___y_166_; lean_object* v___x_168_; lean_object* v___y_170_; lean_object* v_i_171_; lean_object* v___y_177_; lean_object* v___y_187_; lean_object* v_i_188_; lean_object* v___x_203_; 
v___x_164_ = lean_st_ref_take(v_a_140_);
v___x_168_ = lean_box(0);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v___x_164_, v_fvarId_145_);
switch(lean_obj_tag(v___x_203_))
{
case 0:
{
lean_dec_ref_known(v___x_203_, 3);
v___y_166_ = v___x_164_;
goto v___jp_165_;
}
case 1:
{
lean_object* v_index_204_; lean_object* v_size_205_; lean_object* v_keyArray_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_index_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_index_204_);
lean_dec_ref_known(v___x_203_, 1);
v_size_205_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_size_205_);
v_keyArray_206_ = lean_ctor_get(v___x_164_, 1);
lean_inc_ref(v_keyArray_206_);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_size_205_, v___x_207_);
lean_dec(v_size_205_);
v___x_209_ = lean_array_get_size(v_keyArray_206_);
lean_dec_ref(v_keyArray_206_);
v___x_210_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_index_204_);
goto v___jp_193_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_211_ = lean_unsigned_to_nat(4u);
v___x_212_ = lean_nat_mul(v___x_208_, v___x_211_);
v___x_213_ = lean_unsigned_to_nat(3u);
v___x_214_ = lean_nat_mul(v___x_209_, v___x_213_);
v___x_215_ = lean_nat_dec_le(v___x_212_, v___x_214_);
lean_dec(v___x_214_);
lean_dec(v___x_212_);
if (v___x_215_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_index_204_);
goto v___jp_193_;
}
else
{
lean_object* v___x_216_; 
lean_inc(v_fvarId_145_);
v___x_216_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_164_, v___x_208_, v_index_204_, v_fvarId_145_, v___x_168_);
lean_dec(v_index_204_);
v___y_166_ = v___x_216_;
goto v___jp_165_;
}
}
}
default: 
{
lean_object* v_size_217_; lean_object* v_keyArray_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_size_217_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_size_217_);
v_keyArray_218_ = lean_ctor_get(v___x_164_, 1);
lean_inc_ref(v_keyArray_218_);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_size_217_, v___x_219_);
lean_dec(v_size_217_);
v___x_221_ = lean_array_get_size(v_keyArray_218_);
lean_dec_ref(v_keyArray_218_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v___x_220_);
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(v___x_164_);
lean_dec(v___x_164_);
v___y_177_ = v___x_223_;
goto v___jp_176_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_224_ = lean_unsigned_to_nat(4u);
v___x_225_ = lean_nat_mul(v___x_220_, v___x_224_);
lean_dec(v___x_220_);
v___x_226_ = lean_unsigned_to_nat(3u);
v___x_227_ = lean_nat_mul(v___x_221_, v___x_226_);
v___x_228_ = lean_nat_dec_le(v___x_225_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_225_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(v___x_164_);
lean_dec(v___x_164_);
v___y_177_ = v___x_229_;
goto v___jp_176_;
}
else
{
v___y_177_ = v___x_164_;
goto v___jp_176_;
}
}
}
}
v___jp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_st_ref_put(v_a_140_, v___y_166_);
v___y_148_ = v_a_141_;
v___y_149_ = v_a_142_;
v___y_150_ = v_a_143_;
goto v___jp_147_;
}
v___jp_169_:
{
lean_object* v_size_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_size_172_ = lean_ctor_get(v___y_170_, 0);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_size_172_, v___x_173_);
lean_inc(v_fvarId_145_);
v___x_175_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_170_, v___x_174_, v_i_171_, v_fvarId_145_, v___x_168_);
lean_dec(v_i_171_);
v___y_166_ = v___x_175_;
goto v___jp_165_;
}
v___jp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v___y_177_, v_fvarId_145_);
switch(lean_obj_tag(v___x_178_))
{
case 0:
{
lean_object* v_index_179_; lean_object* v_size_180_; lean_object* v___x_181_; 
v_index_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_index_179_);
lean_dec_ref_known(v___x_178_, 3);
v_size_180_ = lean_ctor_get(v___y_177_, 0);
lean_inc(v_size_180_);
lean_inc(v_fvarId_145_);
v___x_181_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_177_, v_size_180_, v_index_179_, v_fvarId_145_, v___x_168_);
lean_dec(v_index_179_);
v___y_166_ = v___x_181_;
goto v___jp_165_;
}
case 1:
{
lean_object* v_index_182_; 
v_index_182_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_index_182_);
lean_dec_ref_known(v___x_178_, 1);
v___y_170_ = v___y_177_;
v_i_171_ = v_index_182_;
goto v___jp_169_;
}
default: 
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_177_, v___x_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_index_185_; 
v_index_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_index_185_);
lean_dec_ref_known(v___x_184_, 1);
v___y_170_ = v___y_177_;
v_i_171_ = v_index_185_;
goto v___jp_169_;
}
else
{
v___y_166_ = v___y_177_;
goto v___jp_165_;
}
}
}
}
v___jp_186_:
{
lean_object* v_size_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_size_189_ = lean_ctor_get(v___y_187_, 0);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_size_189_, v___x_190_);
lean_inc(v_fvarId_145_);
v___x_192_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_187_, v___x_191_, v_i_188_, v_fvarId_145_, v___x_168_);
lean_dec(v_i_188_);
v___y_166_ = v___x_192_;
goto v___jp_165_;
}
v___jp_193_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(v___x_164_);
lean_dec(v___x_164_);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v___x_194_, v_fvarId_145_);
switch(lean_obj_tag(v___x_195_))
{
case 0:
{
lean_object* v_index_196_; lean_object* v_size_197_; lean_object* v___x_198_; 
v_index_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_195_, 3);
v_size_197_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_size_197_);
lean_inc(v_fvarId_145_);
v___x_198_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_194_, v_size_197_, v_index_196_, v_fvarId_145_, v___x_168_);
lean_dec(v_index_196_);
v___y_166_ = v___x_198_;
goto v___jp_165_;
}
case 1:
{
lean_object* v_index_199_; 
v_index_199_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_index_199_);
lean_dec_ref_known(v___x_195_, 1);
v___y_187_ = v___x_194_;
v_i_188_ = v_index_199_;
goto v___jp_186_;
}
default: 
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_194_, v___x_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_index_202_; 
v_index_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_index_202_);
lean_dec_ref_known(v___x_201_, 1);
v___y_187_ = v___x_194_;
v_i_188_ = v_index_202_;
goto v___jp_186_;
}
else
{
v___y_166_ = v___x_194_;
goto v___jp_165_;
}
}
}
}
}
v___jp_147_:
{
lean_object* v___x_151_; 
lean_inc_ref(v_type_146_);
v___x_151_ = l_Lean_Compiler_LCNF_toMonoType(v_type_146_, v___y_149_, v___y_150_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; uint8_t v___x_153_; lean_object* v___x_154_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = 0;
v___x_154_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v___x_153_, v_param_139_, v_a_152_, v___y_148_);
return v___x_154_;
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v_param_139_);
v_a_155_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_151_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_151_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object* v_param_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec(v_a_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object* v_param_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_237_, v_a_238_, v_a_240_, v_a_241_, v_a_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object* v_param_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Compiler_LCNF_Param_toMono(v_param_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(lean_object* v_00_u03b2_253_, lean_object* v_m_254_, lean_object* v_query_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_m_254_, v_query_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___boxed(lean_object* v_00_u03b2_257_, lean_object* v_m_258_, lean_object* v_query_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(v_00_u03b2_257_, v_m_258_, v_query_259_);
lean_dec(v_query_259_);
lean_dec_ref(v_m_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1(lean_object* v_00_u03b2_261_, lean_object* v_m_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___redArg(v_m_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1___boxed(lean_object* v_00_u03b2_264_, lean_object* v_m_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1(v_00_u03b2_264_, v_m_265_);
lean_dec_ref(v_m_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_object* v_00_u03b2_267_, lean_object* v_m_268_, lean_object* v_query_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_m_268_, v_query_269_, v_x_270_, v_x_271_, v_x_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___boxed(lean_object* v_00_u03b2_275_, lean_object* v_m_276_, lean_object* v_query_277_, lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(v_00_u03b2_275_, v_m_276_, v_query_277_, v_x_278_, v_x_279_, v_x_280_, v_x_281_);
lean_dec(v_query_277_);
lean_dec_ref(v_m_276_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2(lean_object* v_00_u03b2_283_, lean_object* v_init_284_, lean_object* v_b_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___redArg(v_init_284_, v_b_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2___boxed(lean_object* v_00_u03b2_287_, lean_object* v_init_288_, lean_object* v_b_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2(v_00_u03b2_287_, v_init_288_, v_b_289_);
lean_dec_ref(v_b_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_291_, lean_object* v_b_292_, lean_object* v_acc_293_, lean_object* v_i_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___redArg(v_b_292_, v_acc_293_, v_i_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_296_, lean_object* v_b_297_, lean_object* v_acc_298_, lean_object* v_i_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Param_toMono_spec__1_spec__2_spec__3(v_00_u03b2_296_, v_b_297_, v_acc_298_, v_i_299_);
lean_dec_ref(v_b_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object* v_arg_303_, lean_object* v_a_304_){
_start:
{
if (lean_obj_tag(v_arg_303_) == 1)
{
lean_object* v_fvarId_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_fvarId_306_ = lean_ctor_get(v_arg_303_, 0);
v___x_307_ = lean_st_ref_get(v_a_304_);
v___x_308_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_309_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
lean_inc(v_fvarId_306_);
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_308_, v___x_309_, v___x_307_, v_fvarId_306_);
lean_dec(v___x_307_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_arg_303_);
return v___x_311_;
}
else
{
lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_isSharedCheck_319_ = !lean_is_exclusive(v_arg_303_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v_arg_303_, 0);
lean_dec(v_unused_320_);
v___x_313_ = v_arg_303_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_dec(v_arg_303_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 0);
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_arg_303_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object* v_arg_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Compiler_LCNF_argToMono___redArg(v_arg_323_, v_a_324_);
lean_dec(v_a_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object* v_arg_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
if (lean_obj_tag(v_arg_327_) == 1)
{
lean_object* v_fvarId_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_fvarId_334_ = lean_ctor_get(v_arg_327_, 0);
v___x_335_ = lean_st_ref_get(v_a_328_);
v___x_336_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_337_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
lean_inc(v_fvarId_334_);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_336_, v___x_337_, v___x_335_, v_fvarId_334_);
lean_dec(v___x_335_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_arg_327_);
return v___x_339_;
}
else
{
lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_347_; 
v_isSharedCheck_347_ = !lean_is_exclusive(v_arg_327_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_arg_327_, 0);
lean_dec(v_unused_348_);
v___x_341_ = v_arg_327_;
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
else
{
lean_dec(v_arg_327_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_347_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; lean_object* v___x_345_; 
v___x_343_ = lean_box(0);
if (v_isShared_342_ == 0)
{
lean_ctor_set_tag(v___x_341_, 0);
lean_ctor_set(v___x_341_, 0, v___x_343_);
v___x_345_ = v___x_341_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_arg_327_);
v___x_349_ = lean_box(0);
v___x_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object* v_arg_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Compiler_LCNF_argToMono(v_arg_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec_ref(v_a_353_);
lean_dec(v_a_352_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg(lean_object* v_m_359_, lean_object* v_query_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_m_359_, v_query_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_index_362_; lean_object* v_key_363_; lean_object* v_value_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_index_362_ = lean_ctor_get(v___x_361_, 0);
v_key_363_ = lean_ctor_get(v___x_361_, 1);
v_value_364_ = lean_ctor_get(v___x_361_, 2);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_361_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_value_364_);
lean_inc(v_key_363_);
lean_inc(v_index_362_);
lean_dec(v___x_361_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_index_362_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_key_363_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_value_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v___x_372_; 
lean_dec(v___x_361_);
v___x_372_ = lean_box(1);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg___boxed(lean_object* v_m_373_, lean_object* v_query_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg(v_m_373_, v_query_374_);
lean_dec(v_query_374_);
lean_dec_ref(v_m_373_);
return v_res_375_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(lean_object* v_m_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg(v_m_376_, v_a_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
uint8_t v___x_379_; 
lean_dec_ref_known(v___x_378_, 3);
v___x_379_ = 1;
return v___x_379_;
}
else
{
uint8_t v___x_380_; 
v___x_380_ = 0;
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg___boxed(lean_object* v_m_381_, lean_object* v_a_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_m_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(lean_object* v_as_385_, size_t v_sz_386_, size_t v_i_387_, lean_object* v_b_388_, lean_object* v___y_389_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_lt(v_i_387_, v_sz_386_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v_b_388_);
return v___x_392_;
}
else
{
lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_434_; 
v_fst_393_ = lean_ctor_get(v_b_388_, 0);
v_snd_394_ = lean_ctor_get(v_b_388_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_434_ == 0)
{
v___x_396_ = v_b_388_;
v_isShared_397_ = v_isSharedCheck_434_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snd_394_);
lean_inc(v_fst_393_);
lean_dec(v_b_388_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_434_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_monoArg_399_; lean_object* v_remainingType_400_; lean_object* v_a_408_; lean_object* v___y_410_; 
v_a_408_ = lean_array_uget_borrowed(v_as_385_, v_i_387_);
if (lean_obj_tag(v_fst_393_) == 1)
{
lean_object* v_val_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_433_; 
v_val_417_ = lean_ctor_get(v_fst_393_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_fst_393_);
if (v_isSharedCheck_433_ == 0)
{
v___x_419_ = v_fst_393_;
v_isShared_420_ = v_isSharedCheck_433_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_val_417_);
lean_dec(v_fst_393_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_433_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
if (lean_obj_tag(v_val_417_) == 7)
{
lean_object* v_binderType_421_; lean_object* v_body_422_; lean_object* v___x_424_; 
v_binderType_421_ = lean_ctor_get(v_val_417_, 1);
lean_inc_ref(v_binderType_421_);
v_body_422_ = lean_ctor_get(v_val_417_, 2);
lean_inc_ref(v_body_422_);
lean_dec_ref_known(v_val_417_, 3);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_body_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_body_422_);
v___x_424_ = v_reuseFailAlloc_432_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_Expr_isErased(v_binderType_421_);
lean_dec_ref(v_binderType_421_);
if (v___x_425_ == 0)
{
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v_fvarId_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_fvarId_426_ = lean_ctor_get(v_a_408_, 0);
v___x_427_ = lean_st_ref_get(v___y_389_);
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_427_, v_fvarId_426_);
lean_dec(v___x_427_);
if (v___x_428_ == 0)
{
lean_inc_ref(v_a_408_);
v_monoArg_399_ = v_a_408_;
v_remainingType_400_ = v___x_424_;
goto v___jp_398_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
v_monoArg_399_ = v___x_429_;
v_remainingType_400_ = v___x_424_;
goto v___jp_398_;
}
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
v_monoArg_399_ = v___x_430_;
v_remainingType_400_ = v___x_424_;
goto v___jp_398_;
}
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_box(0);
v_monoArg_399_ = v___x_431_;
v_remainingType_400_ = v___x_424_;
goto v___jp_398_;
}
}
}
else
{
lean_del_object(v___x_419_);
lean_dec(v_val_417_);
v___y_410_ = v___y_389_;
goto v___jp_409_;
}
}
}
else
{
lean_dec(v_fst_393_);
v___y_410_ = v___y_389_;
goto v___jp_409_;
}
v___jp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_array_push(v_snd_394_, v_monoArg_399_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_401_);
lean_ctor_set(v___x_396_, 0, v_remainingType_400_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_remainingType_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
size_t v___x_404_; size_t v___x_405_; 
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_387_, v___x_404_);
v_i_387_ = v___x_405_;
v_b_388_ = v___x_403_;
goto _start;
}
}
v___jp_409_:
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
if (lean_obj_tag(v_a_408_) == 1)
{
lean_object* v_fvarId_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_fvarId_412_ = lean_ctor_get(v_a_408_, 0);
v___x_413_ = lean_st_ref_get(v___y_410_);
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_413_, v_fvarId_412_);
lean_dec(v___x_413_);
if (v___x_414_ == 0)
{
lean_inc_ref(v_a_408_);
v_monoArg_399_ = v_a_408_;
v_remainingType_400_ = v___x_411_;
goto v___jp_398_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
v_monoArg_399_ = v___x_415_;
v_remainingType_400_ = v___x_411_;
goto v___jp_398_;
}
}
else
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
v_monoArg_399_ = v___x_416_;
v_remainingType_400_ = v___x_411_;
goto v___jp_398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg___boxed(lean_object* v_as_435_, lean_object* v_sz_436_, lean_object* v_i_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
size_t v_sz_boxed_441_; size_t v_i_boxed_442_; lean_object* v_res_443_; 
v_sz_boxed_441_ = lean_unbox_usize(v_sz_436_);
lean_dec(v_sz_436_);
v_i_boxed_442_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_res_443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_435_, v_sz_boxed_441_, v_i_boxed_442_, v_b_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v_as_435_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType(lean_object* v_args_444_, lean_object* v_type_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_remainingType_452_; lean_object* v___x_453_; lean_object* v_result_454_; lean_object* v___x_455_; size_t v_sz_456_; size_t v___x_457_; lean_object* v___x_458_; 
v_remainingType_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_remainingType_452_, 0, v_type_445_);
v___x_453_ = lean_array_get_size(v_args_444_);
v_result_454_ = lean_mk_empty_array_with_capacity(v___x_453_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_remainingType_452_);
lean_ctor_set(v___x_455_, 1, v_result_454_);
v_sz_456_ = lean_array_size(v_args_444_);
v___x_457_ = ((size_t)0ULL);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_args_444_, v_sz_456_, v___x_457_, v___x_455_, v_a_446_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_snd_463_; lean_object* v___x_465_; 
v_snd_463_ = lean_ctor_get(v_a_459_, 1);
lean_inc(v_snd_463_);
lean_dec(v_a_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v_snd_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_snd_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
v_a_468_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_458_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_458_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType___boxed(lean_object* v_args_476_, lean_object* v_type_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_476_, v_type_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec_ref(v_args_476_);
return v_res_484_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_a_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_486_, v_a_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___boxed(lean_object* v_00_u03b2_489_, lean_object* v_m_490_, lean_object* v_a_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(v_00_u03b2_489_, v_m_490_, v_a_491_);
lean_dec(v_a_491_);
lean_dec_ref(v_m_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(lean_object* v_as_494_, size_t v_sz_495_, size_t v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_494_, v_sz_495_, v_i_496_, v_b_497_, v___y_498_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___boxed(lean_object* v_as_505_, lean_object* v_sz_506_, lean_object* v_i_507_, lean_object* v_b_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
size_t v_sz_boxed_515_; size_t v_i_boxed_516_; lean_object* v_res_517_; 
v_sz_boxed_515_ = lean_unbox_usize(v_sz_506_);
lean_dec(v_sz_506_);
v_i_boxed_516_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_res_517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(v_as_505_, v_sz_boxed_515_, v_i_boxed_516_, v_b_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v_as_505_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0(lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_query_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___redArg(v_m_519_, v_query_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0___boxed(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_query_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_spec__0(v_00_u03b2_522_, v_m_523_, v_query_524_);
lean_dec(v_query_524_);
lean_dec_ref(v_m_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(lean_object* v_a_526_, lean_object* v_b_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_array_530_; lean_object* v_start_531_; lean_object* v_stop_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_553_; 
v_array_530_ = lean_ctor_get(v_a_526_, 0);
v_start_531_ = lean_ctor_get(v_a_526_, 1);
v_stop_532_ = lean_ctor_get(v_a_526_, 2);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_553_ == 0)
{
v___x_534_ = v_a_526_;
v_isShared_535_ = v_isSharedCheck_553_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_stop_532_);
lean_inc(v_start_531_);
lean_inc(v_array_530_);
lean_dec(v_a_526_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_553_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
uint8_t v___x_536_; 
v___x_536_ = lean_nat_dec_lt(v_start_531_, v_stop_532_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_del_object(v___x_534_);
lean_dec(v_stop_532_);
lean_dec(v_start_531_);
lean_dec_ref(v_array_530_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v_b_527_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v___x_539_ = lean_nat_add(v_start_531_, v___x_538_);
lean_inc_ref(v_array_530_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 1, v___x_539_);
v___x_541_ = v___x_534_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_array_530_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_stop_532_);
v___x_541_ = v_reuseFailAlloc_552_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v_a_543_; lean_object* v___x_546_; 
v___x_546_ = lean_array_fget(v_array_530_, v_start_531_);
lean_dec(v_start_531_);
lean_dec_ref(v_array_530_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_fvarId_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_fvarId_547_ = lean_ctor_get(v___x_546_, 0);
v___x_548_ = lean_st_ref_get(v___y_528_);
v___x_549_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_548_, v_fvarId_547_);
lean_dec(v___x_548_);
if (v___x_549_ == 0)
{
v_a_543_ = v___x_546_;
goto v___jp_542_;
}
else
{
lean_object* v___x_550_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_550_ = lean_box(0);
v_a_543_ = v___x_550_;
goto v___jp_542_;
}
}
else
{
lean_object* v___x_551_; 
lean_dec(v___x_546_);
v___x_551_ = lean_box(0);
v_a_543_ = v___x_551_;
goto v___jp_542_;
}
v___jp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_array_push(v_b_527_, v_a_543_);
v_a_526_ = v___x_541_;
v_b_527_ = v___x_544_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg___boxed(lean_object* v_a_554_, lean_object* v_b_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v_a_554_, v_b_555_, v___y_556_);
lean_dec(v___y_556_);
return v_res_558_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0(void){
_start:
{
uint8_t v___x_559_; lean_object* v___x_560_; 
v___x_559_ = 0;
v___x_560_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(lean_object* v_params_561_, lean_object* v_fvarId_562_, lean_object* v_a_563_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_fvarId_567_; uint8_t v___x_568_; 
v___x_565_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_566_ = lean_array_get_borrowed(v___x_565_, v_params_561_, v_a_563_);
v_fvarId_567_ = lean_ctor_get(v___x_566_, 0);
v___x_568_ = l_Lean_instBEqFVarId_beq(v_fvarId_567_, v_fvarId_562_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = lean_nat_add(v_a_563_, v___x_569_);
lean_dec(v_a_563_);
v_a_563_ = v___x_570_;
goto _start;
}
else
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v_a_563_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___boxed(lean_object* v_params_573_, lean_object* v_fvarId_574_, lean_object* v_a_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_573_, v_fvarId_574_, v_a_575_);
lean_dec(v_fvarId_574_);
lean_dec_ref(v_params_573_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(lean_object* v_params_578_, lean_object* v_args_579_, lean_object* v_as_580_, size_t v_sz_581_, size_t v_i_582_, lean_object* v_b_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_a_591_; uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_lt(v_i_582_, v_sz_581_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_b_583_);
return v___x_596_;
}
else
{
lean_object* v_fst_597_; lean_object* v_snd_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_630_; 
v_fst_597_ = lean_ctor_get(v_b_583_, 0);
v_snd_598_ = lean_ctor_get(v_b_583_, 1);
v_isSharedCheck_630_ = !lean_is_exclusive(v_b_583_);
if (v_isSharedCheck_630_ == 0)
{
v___x_600_ = v_b_583_;
v_isShared_601_ = v_isSharedCheck_630_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_snd_598_);
lean_inc(v_fst_597_);
lean_dec(v_b_583_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_630_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_a_602_; 
v_a_602_ = lean_array_uget_borrowed(v_as_580_, v_i_582_);
if (lean_obj_tag(v_a_602_) == 1)
{
lean_object* v_fvarId_603_; lean_object* v___x_604_; 
v_fvarId_603_ = lean_ctor_get(v_a_602_, 0);
v___x_604_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_578_, v_fvarId_603_, v_snd_598_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_a_607_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v___x_614_ = lean_box(0);
v___x_615_ = lean_array_get_borrowed(v___x_614_, v_args_579_, v_a_605_);
if (lean_obj_tag(v___x_615_) == 1)
{
lean_object* v_fvarId_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_fvarId_616_ = lean_ctor_get(v___x_615_, 0);
v___x_617_ = lean_st_ref_get(v___y_584_);
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_617_, v_fvarId_616_);
lean_dec(v___x_617_);
if (v___x_618_ == 0)
{
lean_inc_ref(v___x_615_);
v_a_607_ = v___x_615_;
goto v___jp_606_;
}
else
{
v_a_607_ = v___x_614_;
goto v___jp_606_;
}
}
else
{
v_a_607_ = v___x_614_;
goto v___jp_606_;
}
v___jp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_a_605_, v___x_608_);
lean_dec(v_a_605_);
v___x_610_ = lean_array_push(v_fst_597_, v_a_607_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___x_609_);
lean_ctor_set(v___x_600_, 0, v___x_610_);
v___x_612_ = v___x_600_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_609_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v_a_591_ = v___x_612_;
goto v___jp_590_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_del_object(v___x_600_);
lean_dec(v_fst_597_);
v_a_619_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_604_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_604_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v___x_628_; 
if (v_isShared_601_ == 0)
{
v___x_628_ = v___x_600_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_fst_597_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_snd_598_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_a_591_ = v___x_628_;
goto v___jp_590_;
}
}
}
}
v___jp_590_:
{
size_t v___x_592_; size_t v___x_593_; 
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_add(v_i_582_, v___x_592_);
v_i_582_ = v___x_593_;
v_b_583_ = v_a_591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1___boxed(lean_object* v_params_631_, lean_object* v_args_632_, lean_object* v_as_633_, lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_b_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
size_t v_sz_boxed_643_; size_t v_i_boxed_644_; lean_object* v_res_645_; 
v_sz_boxed_643_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_644_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(v_params_631_, v_args_632_, v_as_633_, v_sz_boxed_643_, v_i_boxed_644_, v_b_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v_as_633_);
lean_dec_ref(v_args_632_);
lean_dec_ref(v_params_631_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg(lean_object* v_args_651_, lean_object* v_params_652_, lean_object* v_redArgs_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; size_t v_sz_662_; size_t v___x_663_; lean_object* v___x_664_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__1));
v_sz_662_ = lean_array_size(v_redArgs_653_);
v___x_663_ = ((size_t)0ULL);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__1(v_params_652_, v_args_651_, v_redArgs_653_, v_sz_662_, v___x_663_, v___x_661_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_fst_666_; lean_object* v_lower_668_; lean_object* v_upper_669_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v_fst_666_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_fst_666_);
lean_dec(v_a_665_);
v___x_672_ = lean_array_get_size(v_params_652_);
v___x_673_ = lean_array_get_size(v_args_651_);
v___x_674_ = lean_nat_dec_le(v___x_672_, v___x_660_);
if (v___x_674_ == 0)
{
v_lower_668_ = v___x_672_;
v_upper_669_ = v___x_673_;
goto v___jp_667_;
}
else
{
v_lower_668_ = v___x_660_;
v_upper_669_ = v___x_673_;
goto v___jp_667_;
}
v___jp_667_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = l_Array_toSubarray___redArg(v_args_651_, v_lower_668_, v_upper_669_);
v___x_671_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v___x_670_, v_fst_666_, v_a_654_);
return v___x_671_;
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_args_651_);
v_a_675_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_664_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_664_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoRedArg___boxed(lean_object* v_args_683_, lean_object* v_params_684_, lean_object* v_redArgs_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_683_, v_params_684_, v_redArgs_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_redArgs_685_);
lean_dec_ref(v_params_684_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(lean_object* v_params_693_, lean_object* v_fvarId_694_, lean_object* v_inst_695_, lean_object* v_a_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg(v_params_693_, v_fvarId_694_, v_a_696_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___boxed(lean_object* v_params_704_, lean_object* v_fvarId_705_, lean_object* v_inst_706_, lean_object* v_a_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0(v_params_704_, v_fvarId_705_, v_inst_706_, v_a_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_708_);
lean_dec(v_fvarId_705_);
lean_dec_ref(v_params_704_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(lean_object* v_inst_715_, lean_object* v_R_716_, lean_object* v_a_717_, lean_object* v_b_718_, lean_object* v_c_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___redArg(v_a_717_, v_b_718_, v___y_720_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2___boxed(lean_object* v_inst_727_, lean_object* v_R_728_, lean_object* v_a_729_, lean_object* v_b_730_, lean_object* v_c_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__2(v_inst_727_, v_R_728_, v_a_729_, v_b_730_, v_c_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object* v_a_739_, lean_object* v_b_740_){
_start:
{
lean_object* v_array_741_; lean_object* v_start_742_; lean_object* v_stop_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_756_; 
v_array_741_ = lean_ctor_get(v_a_739_, 0);
v_start_742_ = lean_ctor_get(v_a_739_, 1);
v_stop_743_ = lean_ctor_get(v_a_739_, 2);
v_isSharedCheck_756_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_756_ == 0)
{
v___x_745_ = v_a_739_;
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_stop_743_);
lean_inc(v_start_742_);
lean_inc(v_array_741_);
lean_dec(v_a_739_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_756_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
uint8_t v___x_747_; 
v___x_747_ = lean_nat_dec_lt(v_start_742_, v_stop_743_);
if (v___x_747_ == 0)
{
lean_del_object(v___x_745_);
lean_dec(v_stop_743_);
lean_dec(v_start_742_);
lean_dec_ref(v_array_741_);
return v_b_740_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_start_742_, v___x_748_);
lean_inc_ref(v_array_741_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_array_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_stop_743_);
v___x_751_ = v_reuseFailAlloc_755_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_array_fget(v_array_741_, v_start_742_);
lean_dec(v_start_742_);
lean_dec_ref(v_array_741_);
v___x_753_ = lean_array_push(v_b_740_, v___x_752_);
v_a_739_ = v___x_751_;
v_b_740_ = v___x_753_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t v_sz_757_, size_t v_i_758_, lean_object* v_bs_759_, lean_object* v___y_760_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v_bs_759_);
return v___x_763_;
}
else
{
lean_object* v_v_764_; lean_object* v___x_765_; lean_object* v_bs_x27_766_; lean_object* v_a_768_; 
v_v_764_ = lean_array_uget(v_bs_759_, v_i_758_);
v___x_765_ = lean_unsigned_to_nat(0u);
v_bs_x27_766_ = lean_array_uset(v_bs_759_, v_i_758_, v___x_765_);
if (lean_obj_tag(v_v_764_) == 1)
{
lean_object* v_fvarId_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_fvarId_773_ = lean_ctor_get(v_v_764_, 0);
v___x_774_ = lean_st_ref_get(v___y_760_);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_774_, v_fvarId_773_);
lean_dec(v___x_774_);
if (v___x_775_ == 0)
{
v_a_768_ = v_v_764_;
goto v___jp_767_;
}
else
{
lean_object* v___x_776_; 
lean_dec_ref_known(v_v_764_, 1);
v___x_776_ = lean_box(0);
v_a_768_ = v___x_776_;
goto v___jp_767_;
}
}
else
{
lean_object* v___x_777_; 
lean_dec(v_v_764_);
v___x_777_ = lean_box(0);
v_a_768_ = v___x_777_;
goto v___jp_767_;
}
v___jp_767_:
{
size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((size_t)1ULL);
v___x_770_ = lean_usize_add(v_i_758_, v___x_769_);
v___x_771_ = lean_array_uset(v_bs_x27_766_, v_i_758_, v_a_768_);
v_i_758_ = v___x_770_;
v_bs_759_ = v___x_771_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object* v_sz_778_, lean_object* v_i_779_, lean_object* v_bs_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
size_t v_sz_boxed_783_; size_t v_i_boxed_784_; lean_object* v_res_785_; 
v_sz_boxed_783_ = lean_unbox_usize(v_sz_778_);
lean_dec(v_sz_778_);
v_i_boxed_784_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_res_785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_boxed_783_, v_i_boxed_784_, v_bs_780_, v___y_781_);
lean_dec(v___y_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object* v_ctorInfo_786_, lean_object* v_args_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_toConstantVal_794_; lean_object* v_numParams_795_; lean_object* v___x_796_; lean_object* v_argsNewParams_797_; lean_object* v_lower_799_; lean_object* v_upper_800_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_toConstantVal_794_ = lean_ctor_get(v_ctorInfo_786_, 0);
lean_inc_ref(v_toConstantVal_794_);
v_numParams_795_ = lean_ctor_get(v_ctorInfo_786_, 3);
lean_inc_n(v_numParams_795_, 2);
lean_dec_ref(v_ctorInfo_786_);
v___x_796_ = lean_box(0);
v_argsNewParams_797_ = lean_mk_array(v_numParams_795_, v___x_796_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_array_get_size(v_args_787_);
v___x_837_ = lean_nat_dec_le(v_numParams_795_, v___x_835_);
if (v___x_837_ == 0)
{
v_lower_799_ = v_numParams_795_;
v_upper_800_ = v___x_836_;
goto v___jp_798_;
}
else
{
lean_dec(v_numParams_795_);
v_lower_799_ = v___x_835_;
v_upper_800_ = v___x_836_;
goto v___jp_798_;
}
v___jp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_801_ = l_Array_toSubarray___redArg(v_args_787_, v_lower_799_, v_upper_800_);
v___x_802_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_803_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v___x_801_, v___x_802_);
v_sz_804_ = lean_array_size(v___x_803_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_804_, v___x_805_, v___x_803_, v_a_788_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_826_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_826_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_826_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_826_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v_name_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_823_; 
v_name_811_ = lean_ctor_get(v_toConstantVal_794_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v_toConstantVal_794_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_824_ = lean_ctor_get(v_toConstantVal_794_, 2);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_toConstantVal_794_, 1);
lean_dec(v_unused_825_);
v___x_813_ = v_toConstantVal_794_;
v_isShared_814_ = v_isSharedCheck_823_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_name_811_);
lean_dec(v_toConstantVal_794_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_823_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
v___x_815_ = l_Array_append___redArg(v_argsNewParams_797_, v_a_807_);
lean_dec(v_a_807_);
v___x_816_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 3);
lean_ctor_set(v___x_813_, 2, v___x_815_);
lean_ctor_set(v___x_813_, 1, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_name_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v___x_815_);
v___x_818_ = v_reuseFailAlloc_822_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
lean_object* v___x_820_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_818_);
v___x_820_ = v___x_809_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec_ref(v_argsNewParams_797_);
lean_dec_ref(v_toConstantVal_794_);
v_a_827_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_806_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_806_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object* v_ctorInfo_838_, lean_object* v_args_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_ctorInfo_838_, v_args_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0(lean_object* v_inst_847_, lean_object* v_R_848_, lean_object* v_a_849_, lean_object* v_b_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v_a_849_, v_b_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t v_sz_852_, size_t v_i_853_, lean_object* v_bs_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_852_, v_i_853_, v_bs_854_, v___y_855_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object* v_sz_862_, lean_object* v_i_863_, lean_object* v_bs_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
size_t v_sz_boxed_871_; size_t v_i_boxed_872_; lean_object* v_res_873_; 
v_sz_boxed_871_ = lean_unbox_usize(v_sz_862_);
lean_dec(v_sz_862_);
v_i_boxed_872_ = lean_unbox_usize(v_i_863_);
lean_dec(v_i_863_);
v_res_873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(v_sz_boxed_871_, v_i_boxed_872_, v_bs_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
return v_res_873_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0(void){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_instMonadEIO(lean_box(0));
return v___x_874_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5(void){
_start:
{
uint8_t v___x_879_; lean_object* v___x_880_; 
v___x_879_ = 0;
v___x_880_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object* v_msg_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_toApplicative_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_952_; 
v___x_888_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_889_ = l_StateRefT_x27_instMonad___redArg(v___x_888_);
v_toApplicative_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___x_889_, 1);
lean_dec(v_unused_953_);
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_952_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_toApplicative_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_952_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_toFunctor_894_; lean_object* v_toSeq_895_; lean_object* v_toSeqLeft_896_; lean_object* v_toSeqRight_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_950_; 
v_toFunctor_894_ = lean_ctor_get(v_toApplicative_890_, 0);
v_toSeq_895_ = lean_ctor_get(v_toApplicative_890_, 2);
v_toSeqLeft_896_ = lean_ctor_get(v_toApplicative_890_, 3);
v_toSeqRight_897_ = lean_ctor_get(v_toApplicative_890_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v_toApplicative_890_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_toApplicative_890_, 1);
lean_dec(v_unused_951_);
v___x_899_ = v_toApplicative_890_;
v_isShared_900_ = v_isSharedCheck_950_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_toSeqRight_897_);
lean_inc(v_toSeqLeft_896_);
lean_inc(v_toSeq_895_);
lean_inc(v_toFunctor_894_);
lean_dec(v_toApplicative_890_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_950_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_910_; 
v___f_901_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_902_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_894_);
v___f_903_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_903_, 0, v_toFunctor_894_);
v___f_904_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_904_, 0, v_toFunctor_894_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v___f_903_);
lean_ctor_set(v___x_905_, 1, v___f_904_);
v___f_906_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_906_, 0, v_toSeqRight_897_);
v___f_907_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_907_, 0, v_toSeqLeft_896_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_908_, 0, v_toSeq_895_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 4, v___f_906_);
lean_ctor_set(v___x_899_, 3, v___f_907_);
lean_ctor_set(v___x_899_, 2, v___f_908_);
lean_ctor_set(v___x_899_, 1, v___f_901_);
lean_ctor_set(v___x_899_, 0, v___x_905_);
v___x_910_ = v___x_899_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___f_901_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___f_908_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v___f_907_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___f_906_);
v___x_910_ = v_reuseFailAlloc_949_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 1, v___f_902_);
lean_ctor_set(v___x_892_, 0, v___x_910_);
v___x_912_ = v___x_892_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___f_902_);
v___x_912_ = v_reuseFailAlloc_948_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_913_; lean_object* v_toApplicative_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_946_; 
v___x_913_ = l_StateRefT_x27_instMonad___redArg(v___x_912_);
v_toApplicative_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_913_, 1);
lean_dec(v_unused_947_);
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_946_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_toApplicative_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_946_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_toFunctor_918_; lean_object* v_toSeq_919_; lean_object* v_toSeqLeft_920_; lean_object* v_toSeqRight_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_944_; 
v_toFunctor_918_ = lean_ctor_get(v_toApplicative_914_, 0);
v_toSeq_919_ = lean_ctor_get(v_toApplicative_914_, 2);
v_toSeqLeft_920_ = lean_ctor_get(v_toApplicative_914_, 3);
v_toSeqRight_921_ = lean_ctor_get(v_toApplicative_914_, 4);
v_isSharedCheck_944_ = !lean_is_exclusive(v_toApplicative_914_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_toApplicative_914_, 1);
lean_dec(v_unused_945_);
v___x_923_ = v_toApplicative_914_;
v_isShared_924_ = v_isSharedCheck_944_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_toSeqRight_921_);
lean_inc(v_toSeqLeft_920_);
lean_inc(v_toSeq_919_);
lean_inc(v_toFunctor_918_);
lean_dec(v_toApplicative_914_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_944_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___f_925_; lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___x_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___x_934_; 
v___f_925_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_926_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_918_);
v___f_927_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_927_, 0, v_toFunctor_918_);
v___f_928_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_928_, 0, v_toFunctor_918_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___f_927_);
lean_ctor_set(v___x_929_, 1, v___f_928_);
v___f_930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_930_, 0, v_toSeqRight_921_);
v___f_931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_931_, 0, v_toSeqLeft_920_);
v___f_932_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_932_, 0, v_toSeq_919_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 4, v___f_930_);
lean_ctor_set(v___x_923_, 3, v___f_931_);
lean_ctor_set(v___x_923_, 2, v___f_932_);
lean_ctor_set(v___x_923_, 1, v___f_925_);
lean_ctor_set(v___x_923_, 0, v___x_929_);
v___x_934_ = v___x_923_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___f_925_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v___f_932_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v___f_931_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v___f_930_);
v___x_934_ = v_reuseFailAlloc_943_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___f_926_);
lean_ctor_set(v___x_916_, 0, v___x_934_);
v___x_936_ = v___x_916_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___f_926_);
v___x_936_ = v_reuseFailAlloc_942_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_15758__overap_940_; lean_object* v___x_941_; 
v___x_937_ = l_StateRefT_x27_instMonad___redArg(v___x_936_);
v___x_938_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_939_ = l_instInhabitedOfMonad___redArg(v___x_937_, v___x_938_);
v___x_15758__overap_940_ = lean_panic_fn_borrowed(v___x_939_, v_msg_881_);
lean_dec(v___x_939_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
v___x_941_ = lean_apply_6(v___x_15758__overap_940_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
return v___x_941_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object* v_upperBound_962_, lean_object* v_args_963_, lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_a_969_; uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_lt(v_a_964_, v_upperBound_962_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec(v_a_964_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_b_965_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_box(0);
v___x_977_ = lean_array_get_borrowed(v___x_976_, v_args_963_, v_a_964_);
if (lean_obj_tag(v___x_977_) == 1)
{
lean_object* v_fvarId_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_fvarId_978_ = lean_ctor_get(v___x_977_, 0);
v___x_979_ = lean_st_ref_get(v___y_966_);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_979_, v_fvarId_978_);
lean_dec(v___x_979_);
if (v___x_980_ == 0)
{
lean_inc_ref(v___x_977_);
v_a_969_ = v___x_977_;
goto v___jp_968_;
}
else
{
v_a_969_ = v___x_976_;
goto v___jp_968_;
}
}
else
{
v_a_969_ = v___x_976_;
goto v___jp_968_;
}
}
v___jp_968_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_array_push(v_b_965_, v_a_969_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_a_964_, v___x_971_);
lean_dec(v_a_964_);
v_a_964_ = v___x_972_;
v_b_965_ = v___x_970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object* v_upperBound_981_, lean_object* v_args_982_, lean_object* v_a_983_, lean_object* v_b_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_981_, v_args_982_, v_a_983_, v_b_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v_args_982_);
lean_dec(v_upperBound_981_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__31(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1042_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1043_ = lean_unsigned_to_nat(6u);
v___x_1044_ = lean_unsigned_to_nat(109u);
v___x_1045_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__29));
v___x_1046_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1047_ = l_mkPanicMessageWithDecl(v___x_1046_, v___x_1045_, v___x_1044_, v___x_1043_, v___x_1042_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
switch(lean_obj_tag(v_e_1069_))
{
case 2:
{
lean_object* v_typeName_1076_; lean_object* v_idx_1077_; lean_object* v_struct_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_typeName_1076_ = lean_ctor_get(v_e_1069_, 0);
v_idx_1077_ = lean_ctor_get(v_e_1069_, 1);
v_struct_1078_ = lean_ctor_get(v_e_1069_, 2);
v___x_1079_ = lean_st_ref_get(v_a_1070_);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_1079_, v_struct_1078_);
lean_dec(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_inc(v_typeName_1076_);
v___x_1081_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_1076_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1101_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1101_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1101_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
if (lean_obj_tag(v_a_1082_) == 1)
{
lean_object* v_val_1086_; lean_object* v_fieldIdx_1087_; uint8_t v___x_1088_; 
lean_inc(v_struct_1078_);
lean_inc(v_idx_1077_);
lean_dec_ref_known(v_e_1069_, 3);
v_val_1086_ = lean_ctor_get(v_a_1082_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v_a_1082_, 1);
v_fieldIdx_1087_ = lean_ctor_get(v_val_1086_, 2);
lean_inc(v_fieldIdx_1087_);
lean_dec(v_val_1086_);
v___x_1088_ = lean_nat_dec_eq(v_fieldIdx_1087_, v_idx_1077_);
lean_dec(v_idx_1077_);
lean_dec(v_fieldIdx_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_dec(v_struct_1078_);
v___x_1089_ = lean_box(1);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1089_);
v___x_1091_ = v___x_1084_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_1094_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_struct_1078_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1094_);
v___x_1096_ = v___x_1084_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v___x_1099_; 
lean_dec(v_a_1082_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v_e_1069_);
v___x_1099_ = v___x_1084_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_e_1069_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref_known(v_e_1069_, 3);
v_a_1102_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1081_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1081_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_dec_ref_known(v_e_1069_, 3);
v___x_1110_ = lean_box(1);
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
case 3:
{
lean_object* v_declName_1112_; lean_object* v_args_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1368_; 
v_declName_1112_ = lean_ctor_get(v_e_1069_, 0);
v_args_1113_ = lean_ctor_get(v_e_1069_, 2);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_e_1069_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v_e_1069_, 1);
lean_dec(v_unused_1369_);
v___x_1115_ = v_e_1069_;
v_isShared_1116_ = v_isSharedCheck_1368_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_args_1113_);
lean_inc(v_declName_1112_);
lean_dec(v_e_1069_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1368_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_type_1118_; lean_object* v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; uint8_t v___y_1155_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_1236_ = lean_name_eq(v_declName_1112_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__6));
v___x_1238_ = lean_name_eq(v_declName_1112_, v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_1240_ = lean_name_eq(v_declName_1112_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_1242_ = lean_name_eq(v_declName_1112_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; uint8_t v___x_1244_; 
v___x_1243_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__13));
v___x_1244_ = lean_name_eq(v_declName_1112_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__16));
v___x_1246_ = lean_name_eq(v_declName_1112_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_1248_ = lean_name_eq(v_declName_1112_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__21));
v___x_1250_ = lean_name_eq(v_declName_1112_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__23));
v___x_1252_ = lean_name_eq(v_declName_1112_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v_env_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_st_ref_get(v_a_1074_);
v_env_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref(v_env_1254_);
lean_dec(v___x_1253_);
lean_inc(v_declName_1112_);
v___x_1255_ = l_Lean_Environment_find_x3f(v_env_1254_, v_declName_1112_, v___x_1252_);
if (lean_obj_tag(v___x_1255_) == 1)
{
lean_object* v_val_1256_; 
v_val_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_val_1256_);
lean_dec_ref_known(v___x_1255_, 1);
if (lean_obj_tag(v_val_1256_) == 6)
{
lean_object* v_val_1257_; lean_object* v_induct_1258_; lean_object* v_numParams_1259_; lean_object* v___x_1260_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v_val_1257_ = lean_ctor_get(v_val_1256_, 0);
lean_inc_ref(v_val_1257_);
lean_dec_ref_known(v_val_1256_, 1);
v_induct_1258_ = lean_ctor_get(v_val_1257_, 1);
v_numParams_1259_ = lean_ctor_get(v_val_1257_, 3);
lean_inc(v_induct_1258_);
v___x_1260_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_1258_, v_a_1073_, v_a_1074_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
if (lean_obj_tag(v_a_1261_) == 1)
{
lean_object* v_val_1262_; lean_object* v_fieldIdx_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
lean_inc(v_numParams_1259_);
lean_dec_ref(v_val_1257_);
v_val_1262_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v_a_1261_, 1);
v_fieldIdx_1263_ = lean_ctor_get(v_val_1262_, 2);
lean_inc(v_fieldIdx_1263_);
lean_dec(v_val_1262_);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_nat_add(v_numParams_1259_, v_fieldIdx_1263_);
lean_dec(v_fieldIdx_1263_);
lean_dec(v_numParams_1259_);
v___x_1266_ = lean_array_get(v___x_1264_, v_args_1113_, v___x_1265_);
lean_dec(v___x_1265_);
lean_dec_ref(v_args_1113_);
v___x_1267_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1266_);
lean_dec(v___x_1266_);
v_e_1069_ = v___x_1267_;
goto _start;
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_a_1261_);
v___x_1269_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_1257_, v_args_1113_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1269_;
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_val_1257_);
lean_dec_ref(v_args_1113_);
v_a_1270_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1260_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1260_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_dec(v_val_1256_);
v___y_1178_ = v_a_1070_;
v___y_1179_ = v_a_1071_;
v___y_1180_ = v_a_1072_;
v___y_1181_ = v_a_1073_;
v___y_1182_ = v_a_1074_;
goto v___jp_1177_;
}
}
else
{
lean_dec(v___x_1255_);
v___y_1178_ = v_a_1070_;
v___y_1179_ = v_a_1071_;
v___y_1180_ = v_a_1072_;
v___y_1181_ = v_a_1073_;
v___y_1182_ = v_a_1074_;
goto v___jp_1177_;
}
}
else
{
size_t v_sz_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v_sz_1278_ = lean_array_size(v_args_1113_);
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1278_, v___x_1279_, v_args_1113_, v_a_1070_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1291_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1291_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1285_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__25));
v___x_1286_ = lean_box(0);
v___x_1287_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1285_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
lean_ctor_set(v___x_1287_, 2, v_a_1281_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1287_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
v_a_1292_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1280_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1280_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
else
{
size_t v_sz_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v_sz_1300_ = lean_array_size(v_args_1113_);
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1300_, v___x_1301_, v_args_1113_, v_a_1070_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1313_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1313_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1307_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__27));
v___x_1308_ = lean_box(0);
v___x_1309_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
lean_ctor_set(v___x_1309_, 2, v_a_1303_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1309_);
v___x_1311_ = v___x_1305_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_a_1314_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1302_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1302_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1115_);
lean_dec_ref(v_args_1113_);
lean_dec(v_declName_1112_);
v___x_1322_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__31, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__31_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__31);
v___x_1323_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_1322_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
return v___x_1323_;
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_del_object(v___x_1115_);
lean_dec_ref(v_args_1113_);
lean_dec(v_declName_1112_);
v___x_1324_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__33));
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_unsigned_to_nat(2u);
v___x_1328_ = lean_array_get_borrowed(v___x_1326_, v_args_1113_, v___x_1327_);
if (lean_obj_tag(v___x_1328_) == 1)
{
lean_object* v_fvarId_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_extraArgs_1333_; lean_object* v___x_1334_; 
v_fvarId_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_fvarId_1329_);
v___x_1330_ = lean_array_get_size(v_args_1113_);
v___x_1331_ = lean_unsigned_to_nat(3u);
v___x_1332_ = lean_nat_sub(v___x_1330_, v___x_1331_);
v_extraArgs_1333_ = lean_mk_empty_array_with_capacity(v___x_1332_);
lean_dec(v___x_1332_);
v___x_1334_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_1330_, v_args_1113_, v___x_1331_, v_extraArgs_1333_, v_a_1070_);
lean_dec_ref(v_args_1113_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_fvarId_1329_);
lean_ctor_set(v___x_1339_, 1, v_a_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_fvarId_1329_);
v_a_1344_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1334_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1334_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v_args_1113_);
v___x_1352_ = lean_box(1);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_unsigned_to_nat(2u);
v___x_1356_ = lean_array_get(v___x_1354_, v_args_1113_, v___x_1355_);
lean_dec_ref(v_args_1113_);
v___x_1357_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1356_);
lean_dec(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = lean_array_get(v___x_1359_, v_args_1113_, v___x_1360_);
lean_dec_ref(v_args_1113_);
v___x_1362_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_1361_);
lean_dec(v___x_1361_);
v___x_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1115_);
lean_dec_ref(v_args_1113_);
lean_dec(v_declName_1112_);
v___x_1364_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__37));
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_del_object(v___x_1115_);
lean_dec_ref(v_args_1113_);
lean_dec(v_declName_1112_);
v___x_1366_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__40));
v___x_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
return v___x_1367_;
}
v___jp_1117_:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_1113_, v_type_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec_ref(v_args_1113_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1136_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 2, v_a_1125_);
lean_ctor_set(v___x_1115_, 1, v___x_1129_);
v___x_1131_ = v___x_1115_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_declName_1112_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_a_1125_);
v___x_1131_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1133_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1131_);
v___x_1133_ = v___x_1127_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v_a_1137_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1124_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1124_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
v___jp_1145_:
{
if (v___y_1155_ == 0)
{
lean_object* v_toSignature_1156_; lean_object* v_type_1157_; 
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1149_);
lean_dec_ref(v___y_1147_);
v_toSignature_1156_ = lean_ctor_get(v___y_1146_, 0);
lean_inc_ref(v_toSignature_1156_);
lean_dec_ref(v___y_1146_);
v_type_1157_ = lean_ctor_get(v_toSignature_1156_, 2);
lean_inc_ref(v_type_1157_);
lean_dec_ref(v_toSignature_1156_);
v_type_1118_ = v_type_1157_;
v___y_1119_ = v___y_1152_;
v___y_1120_ = v___y_1153_;
v___y_1121_ = v___y_1148_;
v___y_1122_ = v___y_1150_;
v___y_1123_ = v___y_1154_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1158_; 
lean_dec_ref(v___y_1146_);
lean_del_object(v___x_1115_);
lean_dec(v_declName_1112_);
v___x_1158_ = l_Lean_Compiler_LCNF_argsToMonoRedArg(v_args_1113_, v___y_1149_, v___y_1147_, v___y_1152_, v___y_1153_, v___y_1148_, v___y_1150_, v___y_1154_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v___y_1149_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1168_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1168_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1168_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1163_ = lean_box(0);
v___x_1164_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1164_, 0, v___y_1151_);
lean_ctor_set(v___x_1164_, 1, v___x_1163_);
lean_ctor_set(v___x_1164_, 2, v_a_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1164_);
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec(v___y_1151_);
v_a_1169_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1158_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1158_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
v___jp_1177_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_st_ref_get(v___y_1182_);
lean_dec(v___x_1183_);
lean_inc(v_declName_1112_);
v___x_1184_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1112_, v___y_1182_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
if (lean_obj_tag(v_a_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v_toSignature_1187_; lean_object* v_value_1188_; lean_object* v_type_1189_; lean_object* v_params_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_val_1186_ = lean_ctor_get(v_a_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v_a_1185_, 1);
v_toSignature_1187_ = lean_ctor_get(v_val_1186_, 0);
v_value_1188_ = lean_ctor_get(v_val_1186_, 1);
v_type_1189_ = lean_ctor_get(v_toSignature_1187_, 2);
v_params_1190_ = lean_ctor_get(v_toSignature_1187_, 3);
lean_inc_ref(v_params_1190_);
v___x_1191_ = lean_array_get_size(v_params_1190_);
v___x_1192_ = lean_array_get_size(v_args_1113_);
v___x_1193_ = lean_nat_dec_le(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_inc_ref(v_type_1189_);
lean_dec_ref(v_params_1190_);
lean_dec(v_val_1186_);
v_type_1118_ = v_type_1189_;
v___y_1119_ = v___y_1178_;
v___y_1120_ = v___y_1179_;
v___y_1121_ = v___y_1180_;
v___y_1122_ = v___y_1181_;
v___y_1123_ = v___y_1182_;
goto v___jp_1117_;
}
else
{
if (lean_obj_tag(v_value_1188_) == 0)
{
lean_object* v_code_1194_; 
v_code_1194_ = lean_ctor_get(v_value_1188_, 0);
if (lean_obj_tag(v_code_1194_) == 0)
{
lean_object* v_decl_1195_; lean_object* v_value_1196_; 
v_decl_1195_ = lean_ctor_get(v_code_1194_, 0);
v_value_1196_ = lean_ctor_get(v_decl_1195_, 3);
if (lean_obj_tag(v_value_1196_) == 3)
{
lean_object* v_k_1197_; 
v_k_1197_ = lean_ctor_get(v_code_1194_, 1);
if (lean_obj_tag(v_k_1197_) == 5)
{
lean_object* v_fvarId_1198_; lean_object* v_declName_1199_; lean_object* v_args_1200_; lean_object* v_fvarId_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v_fvarId_1198_ = lean_ctor_get(v_decl_1195_, 0);
v_declName_1199_ = lean_ctor_get(v_value_1196_, 0);
v_args_1200_ = lean_ctor_get(v_value_1196_, 2);
lean_inc_ref(v_args_1200_);
v_fvarId_1201_ = lean_ctor_get(v_k_1197_, 0);
v___x_1202_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__1));
lean_inc(v_declName_1112_);
v___x_1203_ = l_Lean_Name_append(v_declName_1112_, v___x_1202_);
v___x_1204_ = lean_name_eq(v_declName_1199_, v___x_1203_);
if (v___x_1204_ == 0)
{
v___y_1146_ = v_val_1186_;
v___y_1147_ = v_args_1200_;
v___y_1148_ = v___y_1180_;
v___y_1149_ = v_params_1190_;
v___y_1150_ = v___y_1181_;
v___y_1151_ = v___x_1203_;
v___y_1152_ = v___y_1178_;
v___y_1153_ = v___y_1179_;
v___y_1154_ = v___y_1182_;
v___y_1155_ = v___x_1204_;
goto v___jp_1145_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_instBEqFVarId_beq(v_fvarId_1201_, v_fvarId_1198_);
v___y_1146_ = v_val_1186_;
v___y_1147_ = v_args_1200_;
v___y_1148_ = v___y_1180_;
v___y_1149_ = v_params_1190_;
v___y_1150_ = v___y_1181_;
v___y_1151_ = v___x_1203_;
v___y_1152_ = v___y_1178_;
v___y_1153_ = v___y_1179_;
v___y_1154_ = v___y_1182_;
v___y_1155_ = v___x_1205_;
goto v___jp_1145_;
}
}
else
{
lean_inc_ref(v_type_1189_);
lean_dec_ref(v_params_1190_);
lean_dec(v_val_1186_);
v_type_1118_ = v_type_1189_;
v___y_1119_ = v___y_1178_;
v___y_1120_ = v___y_1179_;
v___y_1121_ = v___y_1180_;
v___y_1122_ = v___y_1181_;
v___y_1123_ = v___y_1182_;
goto v___jp_1117_;
}
}
else
{
lean_inc_ref(v_type_1189_);
lean_dec_ref(v_params_1190_);
lean_dec(v_val_1186_);
v_type_1118_ = v_type_1189_;
v___y_1119_ = v___y_1178_;
v___y_1120_ = v___y_1179_;
v___y_1121_ = v___y_1180_;
v___y_1122_ = v___y_1181_;
v___y_1123_ = v___y_1182_;
goto v___jp_1117_;
}
}
else
{
lean_inc_ref(v_type_1189_);
lean_dec_ref(v_params_1190_);
lean_dec(v_val_1186_);
v_type_1118_ = v_type_1189_;
v___y_1119_ = v___y_1178_;
v___y_1120_ = v___y_1179_;
v___y_1121_ = v___y_1180_;
v___y_1122_ = v___y_1181_;
v___y_1123_ = v___y_1182_;
goto v___jp_1117_;
}
}
else
{
lean_inc_ref(v_type_1189_);
lean_dec_ref(v_params_1190_);
lean_dec(v_val_1186_);
v_type_1118_ = v_type_1189_;
v___y_1119_ = v___y_1178_;
v___y_1120_ = v___y_1179_;
v___y_1121_ = v___y_1180_;
v___y_1122_ = v___y_1181_;
v___y_1123_ = v___y_1182_;
goto v___jp_1117_;
}
}
}
else
{
size_t v_sz_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
lean_dec(v_a_1185_);
lean_del_object(v___x_1115_);
v_sz_1206_ = lean_array_size(v_args_1113_);
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1206_, v___x_1207_, v_args_1113_, v___y_1178_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1218_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1218_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1214_, 0, v_declName_1112_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
lean_ctor_set(v___x_1214_, 2, v_a_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v___x_1214_);
v___x_1216_ = v___x_1211_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_declName_1112_);
v_a_1219_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1208_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1208_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_del_object(v___x_1115_);
lean_dec_ref(v_args_1113_);
lean_dec(v_declName_1112_);
v_a_1227_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1184_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1184_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_1370_; lean_object* v_args_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1401_; 
v_fvarId_1370_ = lean_ctor_get(v_e_1069_, 0);
v_args_1371_ = lean_ctor_get(v_e_1069_, 1);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_e_1069_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1373_ = v_e_1069_;
v_isShared_1374_ = v_isSharedCheck_1401_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_args_1371_);
lean_inc(v_fvarId_1370_);
lean_dec(v_e_1069_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1401_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_st_ref_get(v_a_1070_);
v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_1375_, v_fvarId_1370_);
lean_dec(v___x_1375_);
if (v___x_1376_ == 0)
{
size_t v_sz_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v_sz_1377_ = lean_array_size(v_args_1371_);
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_1377_, v___x_1378_, v_args_1371_, v_a_1070_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1390_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1390_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v_a_1380_);
v___x_1385_ = v___x_1373_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_fvarId_1370_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1387_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1385_);
v___x_1387_ = v___x_1382_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1373_);
lean_dec(v_fvarId_1370_);
v_a_1391_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1379_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1379_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
lean_del_object(v___x_1373_);
lean_dec_ref(v_args_1371_);
lean_dec(v_fvarId_1370_);
v___x_1399_ = lean_box(1);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
default: 
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_e_1069_);
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_1411_, lean_object* v_args_1412_, lean_object* v_inst_1413_, lean_object* v_R_1414_, lean_object* v_a_1415_, lean_object* v_b_1416_, lean_object* v_c_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_1411_, v_args_1412_, v_a_1415_, v_b_1416_, v___y_1418_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_1425_, lean_object* v_args_1426_, lean_object* v_inst_1427_, lean_object* v_R_1428_, lean_object* v_a_1429_, lean_object* v_b_1430_, lean_object* v_c_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_1425_, v_args_1426_, v_inst_1427_, v_R_1428_, v_a_1429_, v_b_1430_, v_c_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v_args_1426_);
lean_dec(v_upperBound_1425_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_type_1446_; lean_object* v_value_1447_; lean_object* v___x_1448_; 
v_type_1446_ = lean_ctor_get(v_decl_1439_, 2);
v_value_1447_ = lean_ctor_get(v_decl_1439_, 3);
lean_inc_ref(v_type_1446_);
v___x_1448_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1446_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
lean_inc(v_value_1447_);
v___x_1450_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_1447_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = 0;
v___x_1453_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_1452_, v_decl_1439_, v_a_1449_, v_a_1451_, v_a_1442_);
return v___x_1453_;
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec(v_a_1449_);
lean_dec_ref(v_decl_1439_);
v_a_1454_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1450_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1450_);
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
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_decl_1439_);
v_a_1462_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1448_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1448_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_toApplicative_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1549_; 
v___x_1485_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1486_ = l_StateRefT_x27_instMonad___redArg(v___x_1485_);
v_toApplicative_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1486_, 1);
lean_dec(v_unused_1550_);
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1549_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_toApplicative_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1549_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v_toFunctor_1491_; lean_object* v_toSeq_1492_; lean_object* v_toSeqLeft_1493_; lean_object* v_toSeqRight_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1547_; 
v_toFunctor_1491_ = lean_ctor_get(v_toApplicative_1487_, 0);
v_toSeq_1492_ = lean_ctor_get(v_toApplicative_1487_, 2);
v_toSeqLeft_1493_ = lean_ctor_get(v_toApplicative_1487_, 3);
v_toSeqRight_1494_ = lean_ctor_get(v_toApplicative_1487_, 4);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_toApplicative_1487_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_toApplicative_1487_, 1);
lean_dec(v_unused_1548_);
v___x_1496_ = v_toApplicative_1487_;
v_isShared_1497_ = v_isSharedCheck_1547_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_toSeqRight_1494_);
lean_inc(v_toSeqLeft_1493_);
lean_inc(v_toSeq_1492_);
lean_inc(v_toFunctor_1491_);
lean_dec(v_toApplicative_1487_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1547_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___f_1498_; lean_object* v___f_1499_; lean_object* v___f_1500_; lean_object* v___f_1501_; lean_object* v___x_1502_; lean_object* v___f_1503_; lean_object* v___f_1504_; lean_object* v___f_1505_; lean_object* v___x_1507_; 
v___f_1498_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1499_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1491_);
v___f_1500_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1500_, 0, v_toFunctor_1491_);
v___f_1501_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1501_, 0, v_toFunctor_1491_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___f_1500_);
lean_ctor_set(v___x_1502_, 1, v___f_1501_);
v___f_1503_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1503_, 0, v_toSeqRight_1494_);
v___f_1504_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1504_, 0, v_toSeqLeft_1493_);
v___f_1505_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1505_, 0, v_toSeq_1492_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 4, v___f_1503_);
lean_ctor_set(v___x_1496_, 3, v___f_1504_);
lean_ctor_set(v___x_1496_, 2, v___f_1505_);
lean_ctor_set(v___x_1496_, 1, v___f_1498_);
lean_ctor_set(v___x_1496_, 0, v___x_1502_);
v___x_1507_ = v___x_1496_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___f_1498_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v___f_1505_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v___f_1504_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v___f_1503_);
v___x_1507_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1509_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___f_1499_);
lean_ctor_set(v___x_1489_, 0, v___x_1507_);
v___x_1509_ = v___x_1489_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1507_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___f_1499_);
v___x_1509_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1510_; lean_object* v_toApplicative_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1543_; 
v___x_1510_ = l_StateRefT_x27_instMonad___redArg(v___x_1509_);
v_toApplicative_1511_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1510_, 1);
lean_dec(v_unused_1544_);
v___x_1513_ = v___x_1510_;
v_isShared_1514_ = v_isSharedCheck_1543_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_toApplicative_1511_);
lean_dec(v___x_1510_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1543_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v_toFunctor_1515_; lean_object* v_toSeq_1516_; lean_object* v_toSeqLeft_1517_; lean_object* v_toSeqRight_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1541_; 
v_toFunctor_1515_ = lean_ctor_get(v_toApplicative_1511_, 0);
v_toSeq_1516_ = lean_ctor_get(v_toApplicative_1511_, 2);
v_toSeqLeft_1517_ = lean_ctor_get(v_toApplicative_1511_, 3);
v_toSeqRight_1518_ = lean_ctor_get(v_toApplicative_1511_, 4);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_toApplicative_1511_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v_toApplicative_1511_, 1);
lean_dec(v_unused_1542_);
v___x_1520_ = v_toApplicative_1511_;
v_isShared_1521_ = v_isSharedCheck_1541_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_toSeqRight_1518_);
lean_inc(v_toSeqLeft_1517_);
lean_inc(v_toSeq_1516_);
lean_inc(v_toFunctor_1515_);
lean_dec(v_toApplicative_1511_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1541_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___f_1527_; lean_object* v___f_1528_; lean_object* v___f_1529_; lean_object* v___x_1531_; 
v___f_1522_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1523_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1515_);
v___f_1524_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1524_, 0, v_toFunctor_1515_);
v___f_1525_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1525_, 0, v_toFunctor_1515_);
v___x_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___f_1524_);
lean_ctor_set(v___x_1526_, 1, v___f_1525_);
v___f_1527_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1527_, 0, v_toSeqRight_1518_);
v___f_1528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1528_, 0, v_toSeqLeft_1517_);
v___f_1529_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1529_, 0, v_toSeq_1516_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 4, v___f_1527_);
lean_ctor_set(v___x_1520_, 3, v___f_1528_);
lean_ctor_set(v___x_1520_, 2, v___f_1529_);
lean_ctor_set(v___x_1520_, 1, v___f_1522_);
lean_ctor_set(v___x_1520_, 0, v___x_1526_);
v___x_1531_ = v___x_1520_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___f_1522_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v___f_1529_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v___f_1528_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v___f_1527_);
v___x_1531_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v___f_1523_);
lean_ctor_set(v___x_1513_, 0, v___x_1531_);
v___x_1533_ = v___x_1513_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___f_1523_);
v___x_1533_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_4540__overap_1537_; lean_object* v___x_1538_; 
v___x_1534_ = l_StateRefT_x27_instMonad___redArg(v___x_1533_);
v___x_1535_ = lean_box(0);
v___x_1536_ = l_instInhabitedOfMonad___redArg(v___x_1534_, v___x_1535_);
v___x_4540__overap_1537_ = lean_panic_fn_borrowed(v___x_1536_, v_msg_1478_);
lean_dec(v___x_1536_);
lean_inc(v___y_1483_);
lean_inc_ref(v___y_1482_);
lean_inc(v___y_1481_);
lean_inc_ref(v___y_1480_);
lean_inc(v___y_1479_);
v___x_1538_ = lean_apply_6(v___x_4540__overap_1537_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
return v___x_1538_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
return v_res_1558_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1560_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1561_ = lean_unsigned_to_nat(11u);
v___x_1562_ = lean_unsigned_to_nat(162u);
v___x_1563_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1564_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1565_ = l_mkPanicMessageWithDecl(v___x_1564_, v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1566_, lean_object* v_a_1567_, lean_object* v_b_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_a_1576_; uint8_t v___x_1580_; 
v___x_1580_ = lean_nat_dec_lt(v_a_1567_, v_upperBound_1566_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
lean_dec(v_a_1567_);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v_b_1568_);
return v___x_1581_;
}
else
{
if (lean_obj_tag(v_b_1568_) == 7)
{
lean_object* v_body_1582_; 
v_body_1582_ = lean_ctor_get(v_b_1568_, 2);
lean_inc_ref(v_body_1582_);
lean_dec_ref_known(v_b_1568_, 3);
v_a_1576_ = v_body_1582_;
goto v___jp_1575_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1584_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1583_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_dec_ref_known(v___x_1584_, 1);
v_a_1576_ = v_b_1568_;
goto v___jp_1575_;
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_b_1568_);
lean_dec(v_a_1567_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
v___jp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_nat_add(v_a_1567_, v___x_1577_);
lean_dec(v_a_1567_);
v_a_1567_ = v___x_1578_;
v_b_1568_ = v_a_1576_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1593_, v_a_1594_, v_b_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v_upperBound_1593_);
return v_res_1602_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1603_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_1604_ = lean_unsigned_to_nat(11u);
v___x_1605_ = lean_unsigned_to_nat(170u);
v___x_1606_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1607_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_1608_ = l_mkPanicMessageWithDecl(v___x_1607_, v___x_1606_, v___x_1605_, v___x_1604_, v___x_1603_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1609_, lean_object* v_a_1610_, lean_object* v_b_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_a_1619_; uint8_t v___x_1623_; 
v___x_1623_ = lean_nat_dec_lt(v_a_1610_, v_upperBound_1609_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; 
lean_dec(v_a_1610_);
v___x_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1624_, 0, v_b_1611_);
return v___x_1624_;
}
else
{
lean_object* v_fst_1625_; 
v_fst_1625_ = lean_ctor_get(v_b_1611_, 0);
lean_inc(v_fst_1625_);
if (lean_obj_tag(v_fst_1625_) == 7)
{
lean_object* v_snd_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1659_; 
v_snd_1626_ = lean_ctor_get(v_b_1611_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_b_1611_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_b_1611_, 0);
lean_dec(v_unused_1660_);
v___x_1628_ = v_b_1611_;
v_isShared_1629_ = v_isSharedCheck_1659_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_snd_1626_);
lean_dec(v_b_1611_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1659_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v_binderName_1630_; lean_object* v_binderType_1631_; lean_object* v_body_1632_; lean_object* v___x_1633_; 
v_binderName_1630_ = lean_ctor_get(v_fst_1625_, 0);
lean_inc(v_binderName_1630_);
v_binderType_1631_ = lean_ctor_get(v_fst_1625_, 1);
lean_inc_ref(v_binderType_1631_);
v_body_1632_ = lean_ctor_get(v_fst_1625_, 2);
lean_inc_ref(v_body_1632_);
lean_dec_ref_known(v_fst_1625_, 3);
v___x_1633_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1631_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; uint8_t v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1633_, 1);
v___x_1635_ = 0;
v___x_1636_ = 0;
v___x_1637_ = l_Lean_Compiler_LCNF_mkParam(v___x_1635_, v_binderName_1630_, v_a_1634_, v___x_1636_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = lean_array_push(v_snd_1626_, v_a_1638_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 1, v___x_1639_);
lean_ctor_set(v___x_1628_, 0, v_body_1632_);
v___x_1641_ = v___x_1628_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_body_1632_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v_a_1619_ = v___x_1641_;
goto v___jp_1618_;
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_body_1632_);
lean_del_object(v___x_1628_);
lean_dec(v_snd_1626_);
lean_dec(v_a_1610_);
v_a_1643_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1637_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1637_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_body_1632_);
lean_dec(v_binderName_1630_);
lean_del_object(v___x_1628_);
lean_dec(v_snd_1626_);
lean_dec(v_a_1610_);
v_a_1651_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1633_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1633_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v_snd_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1678_; 
v_snd_1661_ = lean_ctor_get(v_b_1611_, 1);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_b_1611_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v_b_1611_, 0);
lean_dec(v_unused_1679_);
v___x_1663_ = v_b_1611_;
v_isShared_1664_ = v_isSharedCheck_1678_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_snd_1661_);
lean_dec(v_b_1611_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1678_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1665_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1666_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1665_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref_known(v___x_1666_, 1);
if (v_isShared_1664_ == 0)
{
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_fst_1625_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_snd_1661_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
v_a_1619_ = v___x_1668_;
goto v___jp_1618_;
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1663_);
lean_dec(v_snd_1661_);
lean_dec(v_fst_1625_);
lean_dec(v_a_1610_);
v_a_1670_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1666_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1666_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
}
v___jp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(1u);
v___x_1621_ = lean_nat_add(v_a_1610_, v___x_1620_);
lean_dec(v_a_1610_);
v_a_1610_ = v___x_1621_;
v_b_1611_ = v_a_1619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1680_, lean_object* v_a_1681_, lean_object* v_b_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1680_, v_a_1681_, v_b_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec(v_upperBound_1680_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1690_, lean_object* v_numParams_1691_, lean_object* v_numNewFields_1692_, lean_object* v_oldFields_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_unsigned_to_nat(0u);
v___x_1701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1691_, v___x_1700_, v_ctorType_1690_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_array_get_size(v_oldFields_1693_);
v___x_1704_ = lean_nat_add(v___x_1703_, v_numNewFields_1692_);
v___x_1705_ = lean_mk_empty_array_with_capacity(v___x_1704_);
lean_dec(v___x_1704_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1702_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1692_, v___x_1700_, v___x_1706_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1717_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1717_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_snd_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v_snd_1712_ = lean_ctor_get(v_a_1708_, 1);
lean_inc(v_snd_1712_);
lean_dec(v_a_1708_);
v___x_1713_ = l_Array_append___redArg(v_snd_1712_, v_oldFields_1693_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1707_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1707_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1726_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1701_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1701_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1734_, lean_object* v_numParams_1735_, lean_object* v_numNewFields_1736_, lean_object* v_oldFields_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1734_, v_numParams_1735_, v_numNewFields_1736_, v_oldFields_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_oldFields_1737_);
lean_dec(v_numNewFields_1736_);
lean_dec(v_numParams_1735_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1745_, lean_object* v_inst_1746_, lean_object* v_R_1747_, lean_object* v_a_1748_, lean_object* v_b_1749_, lean_object* v_c_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1745_, v_a_1748_, v_b_1749_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1758_, lean_object* v_inst_1759_, lean_object* v_R_1760_, lean_object* v_a_1761_, lean_object* v_b_1762_, lean_object* v_c_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1758_, v_inst_1759_, v_R_1760_, v_a_1761_, v_b_1762_, v_c_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec(v_upperBound_1758_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1771_, lean_object* v_inst_1772_, lean_object* v_R_1773_, lean_object* v_a_1774_, lean_object* v_b_1775_, lean_object* v_c_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1771_, v_a_1774_, v_b_1775_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1784_, lean_object* v_inst_1785_, lean_object* v_R_1786_, lean_object* v_a_1787_, lean_object* v_b_1788_, lean_object* v_c_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1784_, v_inst_1785_, v_R_1786_, v_a_1787_, v_b_1788_, v_c_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec(v_upperBound_1784_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1797_, size_t v_i_1798_, lean_object* v_bs_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_usize_dec_lt(v_i_1798_, v_sz_1797_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_bs_1799_);
return v___x_1806_;
}
else
{
lean_object* v_v_1807_; lean_object* v___x_1808_; 
v_v_1807_ = lean_array_uget_borrowed(v_bs_1799_, v_i_1798_);
lean_inc(v_v_1807_);
v___x_1808_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1807_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; lean_object* v_bs_x27_1811_; size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_unsigned_to_nat(0u);
v_bs_x27_1811_ = lean_array_uset(v_bs_1799_, v_i_1798_, v___x_1810_);
v___x_1812_ = ((size_t)1ULL);
v___x_1813_ = lean_usize_add(v_i_1798_, v___x_1812_);
v___x_1814_ = lean_array_uset(v_bs_x27_1811_, v_i_1798_, v_a_1809_);
v_i_1798_ = v___x_1813_;
v_bs_1799_ = v___x_1814_;
goto _start;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v_bs_1799_);
v_a_1816_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1808_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1808_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1824_, lean_object* v_i_1825_, lean_object* v_bs_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_sz_boxed_1832_; size_t v_i_boxed_1833_; lean_object* v_res_1834_; 
v_sz_boxed_1832_ = lean_unbox_usize(v_sz_1824_);
lean_dec(v_sz_1824_);
v_i_boxed_1833_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1832_, v_i_boxed_1833_, v_bs_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec(v___y_1827_);
return v_res_1834_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
uint8_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = 0;
v___x_1836_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v_toApplicative_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1908_; 
v___x_1844_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1845_ = l_StateRefT_x27_instMonad___redArg(v___x_1844_);
v_toApplicative_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v___x_1845_, 1);
lean_dec(v_unused_1909_);
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1908_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_toApplicative_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1908_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_toFunctor_1850_; lean_object* v_toSeq_1851_; lean_object* v_toSeqLeft_1852_; lean_object* v_toSeqRight_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1906_; 
v_toFunctor_1850_ = lean_ctor_get(v_toApplicative_1846_, 0);
v_toSeq_1851_ = lean_ctor_get(v_toApplicative_1846_, 2);
v_toSeqLeft_1852_ = lean_ctor_get(v_toApplicative_1846_, 3);
v_toSeqRight_1853_ = lean_ctor_get(v_toApplicative_1846_, 4);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_toApplicative_1846_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v_toApplicative_1846_, 1);
lean_dec(v_unused_1907_);
v___x_1855_ = v_toApplicative_1846_;
v_isShared_1856_ = v_isSharedCheck_1906_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_toSeqRight_1853_);
lean_inc(v_toSeqLeft_1852_);
lean_inc(v_toSeq_1851_);
lean_inc(v_toFunctor_1850_);
lean_dec(v_toApplicative_1846_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1906_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___f_1857_; lean_object* v___f_1858_; lean_object* v___f_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___f_1863_; lean_object* v___f_1864_; lean_object* v___x_1866_; 
v___f_1857_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1858_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1850_);
v___f_1859_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1859_, 0, v_toFunctor_1850_);
v___f_1860_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1860_, 0, v_toFunctor_1850_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___f_1859_);
lean_ctor_set(v___x_1861_, 1, v___f_1860_);
v___f_1862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1862_, 0, v_toSeqRight_1853_);
v___f_1863_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1863_, 0, v_toSeqLeft_1852_);
v___f_1864_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1864_, 0, v_toSeq_1851_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 4, v___f_1862_);
lean_ctor_set(v___x_1855_, 3, v___f_1863_);
lean_ctor_set(v___x_1855_, 2, v___f_1864_);
lean_ctor_set(v___x_1855_, 1, v___f_1857_);
lean_ctor_set(v___x_1855_, 0, v___x_1861_);
v___x_1866_ = v___x_1855_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___f_1857_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___f_1864_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v___f_1863_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v___f_1862_);
v___x_1866_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___f_1858_);
lean_ctor_set(v___x_1848_, 0, v___x_1866_);
v___x_1868_ = v___x_1848_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___f_1858_);
v___x_1868_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v_toApplicative_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1902_; 
v___x_1869_ = l_StateRefT_x27_instMonad___redArg(v___x_1868_);
v_toApplicative_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1902_ == 0)
{
lean_object* v_unused_1903_; 
v_unused_1903_ = lean_ctor_get(v___x_1869_, 1);
lean_dec(v_unused_1903_);
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1902_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_toApplicative_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1902_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_toFunctor_1874_; lean_object* v_toSeq_1875_; lean_object* v_toSeqLeft_1876_; lean_object* v_toSeqRight_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1900_; 
v_toFunctor_1874_ = lean_ctor_get(v_toApplicative_1870_, 0);
v_toSeq_1875_ = lean_ctor_get(v_toApplicative_1870_, 2);
v_toSeqLeft_1876_ = lean_ctor_get(v_toApplicative_1870_, 3);
v_toSeqRight_1877_ = lean_ctor_get(v_toApplicative_1870_, 4);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_toApplicative_1870_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_toApplicative_1870_, 1);
lean_dec(v_unused_1901_);
v___x_1879_ = v_toApplicative_1870_;
v_isShared_1880_ = v_isSharedCheck_1900_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_toSeqRight_1877_);
lean_inc(v_toSeqLeft_1876_);
lean_inc(v_toSeq_1875_);
lean_inc(v_toFunctor_1874_);
lean_dec(v_toApplicative_1870_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1900_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___f_1881_; lean_object* v___f_1882_; lean_object* v___f_1883_; lean_object* v___f_1884_; lean_object* v___x_1885_; lean_object* v___f_1886_; lean_object* v___f_1887_; lean_object* v___f_1888_; lean_object* v___x_1890_; 
v___f_1881_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1882_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1874_);
v___f_1883_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1883_, 0, v_toFunctor_1874_);
v___f_1884_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1884_, 0, v_toFunctor_1874_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___f_1883_);
lean_ctor_set(v___x_1885_, 1, v___f_1884_);
v___f_1886_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1886_, 0, v_toSeqRight_1877_);
v___f_1887_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1887_, 0, v_toSeqLeft_1876_);
v___f_1888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1888_, 0, v_toSeq_1875_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 4, v___f_1886_);
lean_ctor_set(v___x_1879_, 3, v___f_1887_);
lean_ctor_set(v___x_1879_, 2, v___f_1888_);
lean_ctor_set(v___x_1879_, 1, v___f_1881_);
lean_ctor_set(v___x_1879_, 0, v___x_1885_);
v___x_1890_ = v___x_1879_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___f_1881_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___f_1888_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v___f_1887_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v___f_1886_);
v___x_1890_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___f_1882_);
lean_ctor_set(v___x_1872_, 0, v___x_1890_);
v___x_1892_ = v___x_1872_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___f_1882_);
v___x_1892_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_48580__overap_1896_; lean_object* v___x_1897_; 
v___x_1893_ = l_StateRefT_x27_instMonad___redArg(v___x_1892_);
v___x_1894_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1895_ = l_instInhabitedOfMonad___redArg(v___x_1893_, v___x_1894_);
v___x_48580__overap_1896_ = lean_panic_fn_borrowed(v___x_1895_, v_msg_1837_);
lean_dec(v___x_1895_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v___y_1838_);
v___x_1897_ = lean_apply_6(v___x_48580__overap_1896_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, lean_box(0));
return v___x_1897_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
lean_dec(v___y_1911_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1920_ = lean_panic_fn_borrowed(v___x_1919_, v_msg_1918_);
return v___x_1920_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
uint8_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = 0;
v___x_1922_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_toApplicative_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1994_; 
v___x_1930_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1931_ = l_StateRefT_x27_instMonad___redArg(v___x_1930_);
v_toApplicative_1932_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1931_, 1);
lean_dec(v_unused_1995_);
v___x_1934_ = v___x_1931_;
v_isShared_1935_ = v_isSharedCheck_1994_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_toApplicative_1932_);
lean_dec(v___x_1931_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1994_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_toFunctor_1936_; lean_object* v_toSeq_1937_; lean_object* v_toSeqLeft_1938_; lean_object* v_toSeqRight_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1992_; 
v_toFunctor_1936_ = lean_ctor_get(v_toApplicative_1932_, 0);
v_toSeq_1937_ = lean_ctor_get(v_toApplicative_1932_, 2);
v_toSeqLeft_1938_ = lean_ctor_get(v_toApplicative_1932_, 3);
v_toSeqRight_1939_ = lean_ctor_get(v_toApplicative_1932_, 4);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_toApplicative_1932_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_toApplicative_1932_, 1);
lean_dec(v_unused_1993_);
v___x_1941_ = v_toApplicative_1932_;
v_isShared_1942_ = v_isSharedCheck_1992_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_toSeqRight_1939_);
lean_inc(v_toSeqLeft_1938_);
lean_inc(v_toSeq_1937_);
lean_inc(v_toFunctor_1936_);
lean_dec(v_toApplicative_1932_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1992_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___f_1943_; lean_object* v___f_1944_; lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___x_1952_; 
v___f_1943_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1944_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1936_);
v___f_1945_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1945_, 0, v_toFunctor_1936_);
v___f_1946_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1946_, 0, v_toFunctor_1936_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___f_1945_);
lean_ctor_set(v___x_1947_, 1, v___f_1946_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toSeqRight_1939_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toSeqLeft_1938_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toSeq_1937_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 4, v___f_1948_);
lean_ctor_set(v___x_1941_, 3, v___f_1949_);
lean_ctor_set(v___x_1941_, 2, v___f_1950_);
lean_ctor_set(v___x_1941_, 1, v___f_1943_);
lean_ctor_set(v___x_1941_, 0, v___x_1947_);
v___x_1952_ = v___x_1941_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1947_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___f_1943_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v___f_1950_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v___f_1949_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v___f_1948_);
v___x_1952_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v___f_1944_);
lean_ctor_set(v___x_1934_, 0, v___x_1952_);
v___x_1954_ = v___x_1934_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___f_1944_);
v___x_1954_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v_toApplicative_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1988_; 
v___x_1955_ = l_StateRefT_x27_instMonad___redArg(v___x_1954_);
v_toApplicative_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1955_, 1);
lean_dec(v_unused_1989_);
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1988_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_toApplicative_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1988_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v_toFunctor_1960_; lean_object* v_toSeq_1961_; lean_object* v_toSeqLeft_1962_; lean_object* v_toSeqRight_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1986_; 
v_toFunctor_1960_ = lean_ctor_get(v_toApplicative_1956_, 0);
v_toSeq_1961_ = lean_ctor_get(v_toApplicative_1956_, 2);
v_toSeqLeft_1962_ = lean_ctor_get(v_toApplicative_1956_, 3);
v_toSeqRight_1963_ = lean_ctor_get(v_toApplicative_1956_, 4);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_toApplicative_1956_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v_toApplicative_1956_, 1);
lean_dec(v_unused_1987_);
v___x_1965_ = v_toApplicative_1956_;
v_isShared_1966_ = v_isSharedCheck_1986_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_toSeqRight_1963_);
lean_inc(v_toSeqLeft_1962_);
lean_inc(v_toSeq_1961_);
lean_inc(v_toFunctor_1960_);
lean_dec(v_toApplicative_1956_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1986_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___f_1967_; lean_object* v___f_1968_; lean_object* v___f_1969_; lean_object* v___f_1970_; lean_object* v___x_1971_; lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___x_1976_; 
v___f_1967_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1968_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1960_);
v___f_1969_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1969_, 0, v_toFunctor_1960_);
v___f_1970_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1970_, 0, v_toFunctor_1960_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___f_1969_);
lean_ctor_set(v___x_1971_, 1, v___f_1970_);
v___f_1972_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1972_, 0, v_toSeqRight_1963_);
v___f_1973_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1973_, 0, v_toSeqLeft_1962_);
v___f_1974_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1974_, 0, v_toSeq_1961_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 4, v___f_1972_);
lean_ctor_set(v___x_1965_, 3, v___f_1973_);
lean_ctor_set(v___x_1965_, 2, v___f_1974_);
lean_ctor_set(v___x_1965_, 1, v___f_1967_);
lean_ctor_set(v___x_1965_, 0, v___x_1971_);
v___x_1976_ = v___x_1965_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___f_1967_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v___f_1974_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v___f_1973_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v___f_1972_);
v___x_1976_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1978_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___f_1968_);
lean_ctor_set(v___x_1958_, 0, v___x_1976_);
v___x_1978_ = v___x_1958_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v___f_1968_);
v___x_1978_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_48595__overap_1982_; lean_object* v___x_1983_; 
v___x_1979_ = l_StateRefT_x27_instMonad___redArg(v___x_1978_);
v___x_1980_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1981_ = l_instInhabitedOfMonad___redArg(v___x_1979_, v___x_1980_);
v___x_48595__overap_1982_ = lean_panic_fn_borrowed(v___x_1981_, v_msg_1923_);
lean_dec(v___x_1981_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v___y_1925_);
lean_inc(v___y_1924_);
v___x_1983_ = lean_apply_6(v___x_48595__overap_1982_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, lean_box(0));
return v___x_1983_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_params_2013_; lean_object* v_type_2014_; lean_object* v_value_2015_; lean_object* v___x_2016_; 
v_params_2013_ = lean_ctor_get(v_decl_2006_, 2);
v_type_2014_ = lean_ctor_get(v_decl_2006_, 3);
v_value_2015_ = lean_ctor_get(v_decl_2006_, 4);
lean_inc_ref(v_type_2014_);
v___x_2016_ = l_Lean_Compiler_LCNF_toMonoType(v_type_2014_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; size_t v_sz_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v_sz_2018_ = lean_array_size(v_params_2013_);
v___x_2019_ = ((size_t)0ULL);
lean_inc_ref(v_params_2013_);
v___x_2020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2018_, v___x_2019_, v_params_2013_, v_a_2007_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
lean_inc_ref(v_value_2015_);
v___x_2022_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_2015_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = 0;
v___x_2025_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_2024_, v_decl_2006_, v_a_2017_, v_a_2021_, v_a_2023_, v_a_2009_);
return v___x_2025_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_a_2021_);
lean_dec(v_a_2017_);
lean_dec_ref(v_decl_2006_);
v_a_2026_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2022_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2022_);
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
lean_dec(v_a_2017_);
lean_dec_ref(v_decl_2006_);
v_a_2034_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2020_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2020_);
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
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_decl_2006_);
v_a_2042_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2016_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2016_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2052_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2053_ = lean_unsigned_to_nat(9u);
v___x_2054_ = lean_unsigned_to_nat(641u);
v___x_2055_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__1));
v___x_2056_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_2057_ = l_mkPanicMessageWithDecl(v___x_2056_, v___x_2055_, v___x_2054_, v___x_2053_, v___x_2052_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2060_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_2061_ = lean_unsigned_to_nat(66u);
v___x_2062_ = lean_unsigned_to_nat(441u);
v___x_2063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_2064_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2065_ = l_mkPanicMessageWithDecl(v___x_2064_, v___x_2063_, v___x_2062_, v___x_2061_, v___x_2060_);
return v___x_2065_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2066_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2067_ = lean_unsigned_to_nat(27u);
v___x_2068_ = lean_unsigned_to_nat(393u);
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_2070_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2071_ = l_mkPanicMessageWithDecl(v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_);
return v___x_2071_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2084_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_2085_ = lean_unsigned_to_nat(70u);
v___x_2086_ = lean_unsigned_to_nat(451u);
v___x_2087_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_2088_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2089_ = l_mkPanicMessageWithDecl(v___x_2088_, v___x_2087_, v___x_2086_, v___x_2085_, v___x_2084_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_2093_, uint8_t v___x_2094_, size_t v_sz_2095_, size_t v_i_2096_, lean_object* v_bs_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
uint8_t v___x_2104_; 
v___x_2104_ = lean_usize_dec_lt(v_i_2096_, v_sz_2095_);
if (v___x_2104_ == 0)
{
lean_object* v___x_2105_; 
lean_dec_ref(v___x_2093_);
v___x_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2105_, 0, v_bs_2097_);
return v___x_2105_;
}
else
{
lean_object* v_v_2106_; lean_object* v___x_2107_; lean_object* v_bs_x27_2108_; lean_object* v_a_2110_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; 
v_v_2106_ = lean_array_uget(v_bs_2097_, v_i_2096_);
v___x_2107_ = lean_unsigned_to_nat(0u);
v_bs_x27_2108_ = lean_array_uset(v_bs_2097_, v_i_2096_, v___x_2107_);
if (lean_obj_tag(v_v_2106_) == 0)
{
lean_object* v_ctorName_2132_; lean_object* v_params_2133_; lean_object* v_code_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2172_; 
v_ctorName_2132_ = lean_ctor_get(v_v_2106_, 0);
v_params_2133_ = lean_ctor_get(v_v_2106_, 1);
v_code_2134_ = lean_ctor_get(v_v_2106_, 2);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_v_2106_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2136_ = v_v_2106_;
v_isShared_2137_ = v_isSharedCheck_2172_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_code_2134_);
lean_inc(v_params_2133_);
lean_inc(v_ctorName_2132_);
lean_dec(v_v_2106_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2172_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_2139_ = l_Lean_Name_append(v_ctorName_2132_, v___x_2138_);
lean_inc(v___x_2139_);
lean_inc_ref(v___x_2093_);
v___x_2140_ = l_Lean_Environment_find_x3f(v___x_2093_, v___x_2139_, v___x_2094_);
if (lean_obj_tag(v___x_2140_) == 1)
{
lean_object* v_val_2141_; 
v_val_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_val_2141_);
lean_dec_ref_known(v___x_2140_, 1);
if (lean_obj_tag(v_val_2141_) == 6)
{
lean_object* v_val_2142_; lean_object* v_toConstantVal_2143_; lean_object* v_numParams_2144_; lean_object* v_numFields_2145_; lean_object* v_type_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_val_2142_ = lean_ctor_get(v_val_2141_, 0);
lean_inc_ref(v_val_2142_);
lean_dec_ref_known(v_val_2141_, 1);
v_toConstantVal_2143_ = lean_ctor_get(v_val_2142_, 0);
lean_inc_ref(v_toConstantVal_2143_);
v_numParams_2144_ = lean_ctor_get(v_val_2142_, 3);
lean_inc(v_numParams_2144_);
v_numFields_2145_ = lean_ctor_get(v_val_2142_, 4);
lean_inc(v_numFields_2145_);
lean_dec_ref(v_val_2142_);
v_type_2146_ = lean_ctor_get(v_toConstantVal_2143_, 2);
lean_inc_ref(v_type_2146_);
lean_dec_ref(v_toConstantVal_2143_);
v___x_2147_ = lean_array_get_size(v_params_2133_);
v___x_2148_ = lean_nat_sub(v_numFields_2145_, v___x_2147_);
lean_dec(v_numFields_2145_);
v___x_2149_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_2146_, v_numParams_2144_, v___x_2148_, v_params_2133_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec_ref(v_params_2133_);
lean_dec(v___x_2148_);
lean_dec(v_numParams_2144_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
v___x_2151_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2134_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc(v_a_2152_);
lean_dec_ref_known(v___x_2151_, 1);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 2, v_a_2152_);
lean_ctor_set(v___x_2136_, 1, v_a_2150_);
lean_ctor_set(v___x_2136_, 0, v___x_2139_);
v___x_2154_ = v___x_2136_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2150_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_a_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
v_a_2110_ = v___x_2154_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2150_);
lean_dec(v___x_2139_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_bs_x27_2108_);
lean_dec_ref(v___x_2093_);
v_a_2156_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2151_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2151_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v___x_2139_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_code_2134_);
lean_dec_ref(v_bs_x27_2108_);
lean_dec_ref(v___x_2093_);
v_a_2164_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2149_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2149_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_dec(v_val_2141_);
lean_dec(v___x_2139_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_code_2134_);
lean_dec_ref(v_params_2133_);
v___y_2116_ = v___y_2098_;
v___y_2117_ = v___y_2099_;
v___y_2118_ = v___y_2100_;
v___y_2119_ = v___y_2101_;
v___y_2120_ = v___y_2102_;
goto v___jp_2115_;
}
}
else
{
lean_dec(v___x_2140_);
lean_dec(v___x_2139_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_code_2134_);
lean_dec_ref(v_params_2133_);
v___y_2116_ = v___y_2098_;
v___y_2117_ = v___y_2099_;
v___y_2118_ = v___y_2100_;
v___y_2119_ = v___y_2101_;
v___y_2120_ = v___y_2102_;
goto v___jp_2115_;
}
}
}
else
{
lean_object* v_code_2173_; lean_object* v___x_2174_; 
v_code_2173_ = lean_ctor_get(v_v_2106_, 0);
lean_inc_ref(v_code_2173_);
v___x_2174_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2173_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2106_, v_a_2175_);
v_a_2110_ = v___x_2176_;
goto v___jp_2109_;
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec_ref_known(v_v_2106_, 1);
lean_dec_ref(v_bs_x27_2108_);
lean_dec_ref(v___x_2093_);
v_a_2177_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2174_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2174_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
v___jp_2109_:
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_add(v_i_2096_, v___x_2111_);
v___x_2113_ = lean_array_uset(v_bs_x27_2108_, v_i_2096_, v_a_2110_);
v_i_2096_ = v___x_2112_;
v_bs_2097_ = v___x_2113_;
goto _start;
}
v___jp_2115_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_2122_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_2121_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v_a_2110_ = v_a_2123_;
goto v___jp_2109_;
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v_bs_x27_2108_);
lean_dec_ref(v___x_2093_);
v_a_2124_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
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
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2230_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2231_ = lean_unsigned_to_nat(2u);
v___x_2232_ = lean_unsigned_to_nat(376u);
v___x_2233_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2234_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2235_ = l_mkPanicMessageWithDecl(v___x_2234_, v___x_2233_, v___x_2232_, v___x_2231_, v___x_2230_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2237_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_2238_ = lean_unsigned_to_nat(2u);
v___x_2239_ = lean_unsigned_to_nat(378u);
v___x_2240_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2241_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2242_ = l_mkPanicMessageWithDecl(v___x_2241_, v___x_2240_, v___x_2239_, v___x_2238_, v___x_2237_);
return v___x_2242_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2244_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_2245_ = lean_unsigned_to_nat(2u);
v___x_2246_ = lean_unsigned_to_nat(379u);
v___x_2247_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2248_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2249_ = l_mkPanicMessageWithDecl(v___x_2248_, v___x_2247_, v___x_2246_, v___x_2245_, v___x_2244_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2250_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2251_ = lean_unsigned_to_nat(41u);
v___x_2252_ = lean_unsigned_to_nat(377u);
v___x_2253_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_2254_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2255_ = l_mkPanicMessageWithDecl(v___x_2254_, v___x_2253_, v___x_2252_, v___x_2251_, v___x_2250_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_2256_, lean_object* v_c_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_discr_2264_; lean_object* v_alts_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2343_; 
v_discr_2264_ = lean_ctor_get(v_c_2257_, 2);
v_alts_2265_ = lean_ctor_get(v_c_2257_, 3);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_c_2257_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; lean_object* v_unused_2345_; 
v_unused_2344_ = lean_ctor_get(v_c_2257_, 1);
lean_dec(v_unused_2344_);
v_unused_2345_ = lean_ctor_get(v_c_2257_, 0);
lean_dec(v_unused_2345_);
v___x_2267_ = v_c_2257_;
v_isShared_2268_ = v_isSharedCheck_2343_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_alts_2265_);
lean_inc(v_discr_2264_);
lean_dec(v_c_2257_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2343_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2269_ = lean_array_get_size(v_alts_2265_);
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_dec_eq(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_del_object(v___x_2267_);
lean_dec_ref(v_alts_2265_);
lean_dec(v_discr_2264_);
v___x_2272_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_2273_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2272_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2273_;
}
else
{
uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2274_ = 0;
v___x_2275_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_array_get(v___x_2275_, v_alts_2265_, v___x_2276_);
lean_dec_ref(v_alts_2265_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_ctorName_2278_; lean_object* v_params_2279_; lean_object* v_code_2280_; lean_object* v_ctorName_2281_; lean_object* v_fieldIdx_2282_; uint8_t v___x_2283_; 
v_ctorName_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_ctorName_2278_);
v_params_2279_ = lean_ctor_get(v___x_2277_, 1);
lean_inc_ref(v_params_2279_);
v_code_2280_ = lean_ctor_get(v___x_2277_, 2);
lean_inc_ref(v_code_2280_);
lean_dec_ref_known(v___x_2277_, 3);
v_ctorName_2281_ = lean_ctor_get(v_info_2256_, 0);
v_fieldIdx_2282_ = lean_ctor_get(v_info_2256_, 2);
v___x_2283_ = lean_name_eq(v_ctorName_2278_, v_ctorName_2281_);
lean_dec(v_ctorName_2278_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v_code_2280_);
lean_dec_ref(v_params_2279_);
lean_del_object(v___x_2267_);
lean_dec(v_discr_2264_);
v___x_2284_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_2285_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2284_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2285_;
}
else
{
lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2286_ = lean_array_get_size(v_params_2279_);
v___x_2287_ = lean_nat_dec_lt(v_fieldIdx_2282_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v_code_2280_);
lean_dec_ref(v_params_2279_);
lean_del_object(v___x_2267_);
lean_dec(v_discr_2264_);
v___x_2288_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_2289_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2288_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2289_;
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2291_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2274_, v_params_2279_, v_a_2260_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_p_2292_; lean_object* v_fvarId_2293_; lean_object* v_binderName_2294_; lean_object* v_type_2295_; lean_object* v___x_2296_; 
lean_dec_ref_known(v___x_2291_, 1);
v_p_2292_ = lean_array_get(v___x_2290_, v_params_2279_, v_fieldIdx_2282_);
lean_dec_ref(v_params_2279_);
v_fvarId_2293_ = lean_ctor_get(v_p_2292_, 0);
lean_inc(v_fvarId_2293_);
v_binderName_2294_ = lean_ctor_get(v_p_2292_, 1);
lean_inc(v_binderName_2294_);
v_type_2295_ = lean_ctor_get(v_p_2292_, 2);
lean_inc_ref(v_type_2295_);
lean_dec(v_p_2292_);
v___x_2296_ = l_Lean_Compiler_LCNF_toMonoType(v_type_2295_, v_a_2261_, v_a_2262_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v_lctx_2299_; lean_object* v_nextIdx_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2324_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
v___x_2298_ = lean_st_ref_take(v_a_2260_);
v_lctx_2299_ = lean_ctor_get(v___x_2298_, 0);
v_nextIdx_2300_ = lean_ctor_get(v___x_2298_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2302_ = v___x_2298_;
v_isShared_2303_ = v_isSharedCheck_2324_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_nextIdx_2300_);
lean_inc(v_lctx_2299_);
lean_dec(v___x_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2324_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2304_ = ((lean_object*)(l_Lean_Compiler_LCNF_argsToMonoRedArg___closed__0));
v___x_2305_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_discr_2264_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 3, v___x_2305_);
lean_ctor_set(v___x_2267_, 2, v_a_2297_);
lean_ctor_set(v___x_2267_, 1, v_binderName_2294_);
lean_ctor_set(v___x_2267_, 0, v_fvarId_2293_);
v___x_2307_ = v___x_2267_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fvarId_2293_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_binderName_2294_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_a_2297_);
lean_ctor_set(v_reuseFailAlloc_2323_, 3, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
lean_inc_ref(v___x_2307_);
v___x_2308_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2274_, v_lctx_2299_, v___x_2307_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2308_);
v___x_2310_ = v___x_2302_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_nextIdx_2300_);
v___x_2310_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_st_ref_put(v_a_2260_, v___x_2310_);
v___x_2312_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2280_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2321_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2307_);
lean_ctor_set(v___x_2317_, 1, v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_dec_ref(v___x_2307_);
return v___x_2312_;
}
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v_binderName_2294_);
lean_dec(v_fvarId_2293_);
lean_dec_ref(v_code_2280_);
lean_del_object(v___x_2267_);
lean_dec(v_discr_2264_);
v_a_2325_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2296_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2296_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v_code_2280_);
lean_dec_ref(v_params_2279_);
lean_del_object(v___x_2267_);
lean_dec(v_discr_2264_);
v_a_2333_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2291_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2291_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v___x_2277_);
lean_del_object(v___x_2267_);
lean_dec(v_discr_2264_);
v___x_2341_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_2342_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2341_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_2346_, size_t v_i_2347_, lean_object* v_bs_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_usize_dec_lt(v_i_2347_, v_sz_2346_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_bs_2348_);
return v___x_2356_;
}
else
{
lean_object* v_v_2357_; lean_object* v___x_2358_; lean_object* v_bs_x27_2359_; lean_object* v_a_2361_; 
v_v_2357_ = lean_array_uget(v_bs_2348_, v_i_2347_);
v___x_2358_ = lean_unsigned_to_nat(0u);
v_bs_x27_2359_ = lean_array_uset(v_bs_2348_, v_i_2347_, v___x_2358_);
if (lean_obj_tag(v_v_2357_) == 0)
{
lean_object* v_params_2366_; lean_object* v_code_2367_; size_t v_sz_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
v_params_2366_ = lean_ctor_get(v_v_2357_, 1);
v_code_2367_ = lean_ctor_get(v_v_2357_, 2);
v_sz_2368_ = lean_array_size(v_params_2366_);
v___x_2369_ = ((size_t)0ULL);
lean_inc_ref(v_params_2366_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_2368_, v___x_2369_, v_params_2366_, v___y_2349_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2372_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref_known(v___x_2370_, 1);
lean_inc_ref(v_code_2367_);
v___x_2372_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2367_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref_known(v___x_2372_, 1);
v___x_2374_ = 0;
v___x_2375_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_2374_, v_v_2357_, v_a_2371_, v_a_2373_);
v_a_2361_ = v___x_2375_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_a_2371_);
lean_dec_ref_known(v_v_2357_, 3);
lean_dec_ref(v_bs_x27_2359_);
v_a_2376_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2372_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2372_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_2357_, 3);
lean_dec_ref(v_bs_x27_2359_);
return v___x_2370_;
}
}
else
{
lean_object* v_code_2384_; lean_object* v___x_2385_; 
v_code_2384_ = lean_ctor_get(v_v_2357_, 0);
lean_inc_ref(v_code_2384_);
v___x_2385_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2384_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2387_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
v___x_2387_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2357_, v_a_2386_);
v_a_2361_ = v___x_2387_;
goto v___jp_2360_;
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref_known(v_v_2357_, 1);
lean_dec_ref(v_bs_x27_2359_);
v_a_2388_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2385_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2385_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
v___jp_2360_:
{
size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2347_, v___x_2362_);
v___x_2364_ = lean_array_uset(v_bs_x27_2359_, v_i_2347_, v_a_2361_);
v_i_2347_ = v___x_2363_;
v_bs_2348_ = v___x_2364_;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2397_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2399_ = lean_unsigned_to_nat(365u);
v___x_2400_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2401_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2402_ = l_mkPanicMessageWithDecl(v___x_2401_, v___x_2400_, v___x_2399_, v___x_2398_, v___x_2397_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_unsigned_to_nat(2u);
v___x_2409_ = lean_mk_empty_array_with_capacity(v___x_2408_);
v___x_2410_ = lean_array_push(v___x_2409_, v___x_2407_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2411_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2412_ = lean_unsigned_to_nat(34u);
v___x_2413_ = lean_unsigned_to_nat(366u);
v___x_2414_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_2415_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2416_ = l_mkPanicMessageWithDecl(v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_, v___x_2411_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v_discr_2424_; lean_object* v_alts_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2494_; 
v_discr_2424_ = lean_ctor_get(v_c_2417_, 2);
v_alts_2425_ = lean_ctor_get(v_c_2417_, 3);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_c_2417_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; lean_object* v_unused_2496_; 
v_unused_2495_ = lean_ctor_get(v_c_2417_, 1);
lean_dec(v_unused_2495_);
v_unused_2496_ = lean_ctor_get(v_c_2417_, 0);
lean_dec(v_unused_2496_);
v___x_2427_ = v_c_2417_;
v_isShared_2428_ = v_isSharedCheck_2494_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_alts_2425_);
lean_inc(v_discr_2424_);
lean_dec(v_c_2417_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2494_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v___x_2429_ = lean_array_get_size(v_alts_2425_);
v___x_2430_ = lean_unsigned_to_nat(1u);
v___x_2431_ = lean_nat_dec_eq(v___x_2429_, v___x_2430_);
if (v___x_2431_ == 0)
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
lean_del_object(v___x_2427_);
lean_dec_ref(v_alts_2425_);
lean_dec(v_discr_2424_);
v___x_2432_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_2433_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2432_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2433_;
}
else
{
uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2434_ = 0;
v___x_2435_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_array_get(v___x_2435_, v_alts_2425_, v___x_2436_);
lean_dec_ref(v_alts_2425_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_params_2438_; lean_object* v_code_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2490_; 
v_params_2438_ = lean_ctor_get(v___x_2437_, 1);
v_code_2439_ = lean_ctor_get(v___x_2437_, 2);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2491_);
v___x_2441_ = v___x_2437_;
v_isShared_2442_ = v_isSharedCheck_2490_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_code_2439_);
lean_inc(v_params_2438_);
lean_dec(v___x_2437_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2490_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2434_, v_params_2438_, v_a_2420_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_fvarId_2447_; lean_object* v_binderName_2448_; lean_object* v_lctx_2449_; lean_object* v_nextIdx_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref_known(v___x_2443_, 1);
v___x_2444_ = lean_st_ref_take(v_a_2420_);
v___x_2445_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2446_ = lean_array_get(v___x_2445_, v_params_2438_, v___x_2436_);
lean_dec_ref(v_params_2438_);
v_fvarId_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_fvarId_2447_);
v_binderName_2448_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_binderName_2448_);
lean_dec(v___x_2446_);
v_lctx_2449_ = lean_ctor_get(v___x_2444_, 0);
v_nextIdx_2450_ = lean_ctor_get(v___x_2444_, 1);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2452_ = v___x_2444_;
v_isShared_2453_ = v_isSharedCheck_2481_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_nextIdx_2450_);
lean_inc(v_lctx_2449_);
lean_dec(v___x_2444_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2481_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2454_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_discr_2424_);
v___x_2457_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_2458_ = lean_array_push(v___x_2457_, v___x_2456_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set_tag(v___x_2441_, 3);
lean_ctor_set(v___x_2441_, 2, v___x_2458_);
lean_ctor_set(v___x_2441_, 1, v___x_2455_);
lean_ctor_set(v___x_2441_, 0, v___x_2454_);
v___x_2460_ = v___x_2441_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2461_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 3, v___x_2460_);
lean_ctor_set(v___x_2427_, 2, v___x_2461_);
lean_ctor_set(v___x_2427_, 1, v_binderName_2448_);
lean_ctor_set(v___x_2427_, 0, v_fvarId_2447_);
v___x_2463_ = v___x_2427_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_fvarId_2447_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_binderName_2448_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v___x_2460_);
v___x_2463_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_inc_ref(v___x_2463_);
v___x_2464_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2434_, v_lctx_2449_, v___x_2463_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2464_);
v___x_2466_ = v___x_2452_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextIdx_2450_);
v___x_2466_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_st_ref_put(v_a_2420_, v___x_2466_);
v___x_2468_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2439_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2471_ = v___x_2468_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2463_);
lean_ctor_set(v___x_2473_, 1, v_a_2469_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
else
{
lean_dec_ref(v___x_2463_);
return v___x_2468_;
}
}
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_del_object(v___x_2441_);
lean_dec_ref(v_code_2439_);
lean_dec_ref(v_params_2438_);
lean_del_object(v___x_2427_);
lean_dec(v_discr_2424_);
v_a_2482_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2443_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2443_);
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
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec(v___x_2437_);
lean_del_object(v___x_2427_);
lean_dec(v_discr_2424_);
v___x_2492_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_2493_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2492_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2493_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2498_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2499_ = lean_unsigned_to_nat(2u);
v___x_2500_ = lean_unsigned_to_nat(345u);
v___x_2501_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2502_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2503_ = l_mkPanicMessageWithDecl(v___x_2502_, v___x_2501_, v___x_2500_, v___x_2499_, v___x_2498_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_2512_ = l_Lean_Expr_const___override(v___x_2511_, v___x_2510_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2513_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2514_ = lean_unsigned_to_nat(34u);
v___x_2515_ = lean_unsigned_to_nat(346u);
v___x_2516_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_2517_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2518_ = l_mkPanicMessageWithDecl(v___x_2517_, v___x_2516_, v___x_2515_, v___x_2514_, v___x_2513_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_discr_2526_; lean_object* v_alts_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_discr_2526_ = lean_ctor_get(v_c_2519_, 2);
v_alts_2527_ = lean_ctor_get(v_c_2519_, 3);
v___x_2528_ = lean_array_get_size(v_alts_2527_);
v___x_2529_ = lean_unsigned_to_nat(1u);
v___x_2530_ = lean_nat_dec_eq(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_2532_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2531_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2532_;
}
else
{
uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = 0;
v___x_2534_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = lean_array_get(v___x_2534_, v_alts_2527_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_params_2537_; lean_object* v_code_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2635_; 
v_params_2537_ = lean_ctor_get(v___x_2536_, 1);
v_code_2538_ = lean_ctor_get(v___x_2536_, 2);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v___x_2536_, 0);
lean_dec(v_unused_2636_);
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2635_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_code_2538_);
lean_inc(v_params_2537_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2635_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2533_, v_params_2537_, v_a_2522_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec_ref_known(v___x_2542_, 1);
v___x_2543_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2544_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2543_, v_a_2522_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
lean_inc(v_discr_2526_);
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_discr_2526_);
v___x_2548_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_2551_ = lean_array_push(v___x_2550_, v___x_2547_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set_tag(v___x_2540_, 3);
lean_ctor_set(v___x_2540_, 2, v___x_2551_);
lean_ctor_set(v___x_2540_, 1, v___x_2549_);
lean_ctor_set(v___x_2540_, 0, v___x_2548_);
v___x_2553_ = v___x_2540_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2555_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2533_, v_a_2545_, v___x_2554_, v___x_2553_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___x_2559_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2558_ = 0;
v___x_2559_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_2533_, v___x_2557_, v___x_2558_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = l_Lean_mkArrow(v___x_2557_, v___x_2554_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v_fvarId_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v_fvarId_2566_; lean_object* v_binderName_2567_; lean_object* v_lctx_2568_; lean_object* v_nextIdx_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2593_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v_fvarId_2563_ = lean_ctor_get(v_a_2556_, 0);
v___x_2564_ = lean_st_ref_take(v_a_2522_);
v___x_2565_ = lean_array_get(v___x_2546_, v_params_2537_, v___x_2535_);
lean_dec_ref(v_params_2537_);
v_fvarId_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_fvarId_2566_);
v_binderName_2567_ = lean_ctor_get(v___x_2565_, 1);
lean_inc(v_binderName_2567_);
lean_dec(v___x_2565_);
v_lctx_2568_ = lean_ctor_get(v___x_2564_, 0);
v_nextIdx_2569_ = lean_ctor_get(v___x_2564_, 1);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2571_ = v___x_2564_;
v_isShared_2572_ = v_isSharedCheck_2593_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_nextIdx_2569_);
lean_inc(v_lctx_2568_);
lean_dec(v___x_2564_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2593_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
lean_inc(v_fvarId_2563_);
v___x_2573_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2573_, 0, v_fvarId_2563_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2556_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_mk_empty_array_with_capacity(v___x_2529_);
v___x_2576_ = lean_array_push(v___x_2575_, v_a_2560_);
v___x_2577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2577_, 0, v_fvarId_2566_);
lean_ctor_set(v___x_2577_, 1, v_binderName_2567_);
lean_ctor_set(v___x_2577_, 2, v___x_2576_);
lean_ctor_set(v___x_2577_, 3, v_a_2562_);
lean_ctor_set(v___x_2577_, 4, v___x_2574_);
lean_inc_ref(v___x_2577_);
v___x_2578_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2533_, v_lctx_2568_, v___x_2577_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2578_);
v___x_2580_ = v___x_2571_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_nextIdx_2569_);
v___x_2580_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2581_ = lean_st_ref_put(v_a_2522_, v___x_2580_);
v___x_2582_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2538_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2591_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2585_ = v___x_2582_;
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2591_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2577_);
lean_ctor_set(v___x_2587_, 1, v_a_2583_);
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2587_);
v___x_2589_ = v___x_2585_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
else
{
lean_dec_ref_known(v___x_2577_, 5);
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_a_2560_);
lean_dec(v_a_2556_);
lean_dec_ref(v_code_2538_);
lean_dec_ref(v_params_2537_);
v_a_2594_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2561_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2561_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
lean_dec(v_a_2556_);
lean_dec_ref(v_code_2538_);
lean_dec_ref(v_params_2537_);
v_a_2602_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2559_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2559_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
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
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec_ref(v_code_2538_);
lean_dec_ref(v_params_2537_);
v_a_2610_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2555_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2555_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_del_object(v___x_2540_);
lean_dec_ref(v_code_2538_);
lean_dec_ref(v_params_2537_);
v_a_2619_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2544_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2544_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2540_);
lean_dec_ref(v_code_2538_);
lean_dec_ref(v_params_2537_);
v_a_2627_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2542_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2542_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_dec(v___x_2536_);
v___x_2637_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2638_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2637_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2638_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2640_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2641_ = lean_unsigned_to_nat(2u);
v___x_2642_ = lean_unsigned_to_nat(334u);
v___x_2643_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2644_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2645_ = l_mkPanicMessageWithDecl(v___x_2644_, v___x_2643_, v___x_2642_, v___x_2641_, v___x_2640_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2650_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2651_ = lean_unsigned_to_nat(34u);
v___x_2652_ = lean_unsigned_to_nat(335u);
v___x_2653_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2654_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2655_ = l_mkPanicMessageWithDecl(v___x_2654_, v___x_2653_, v___x_2652_, v___x_2651_, v___x_2650_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
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
v___x_2671_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2672_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2671_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2672_;
}
else
{
uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2673_ = 0;
v___x_2674_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = lean_array_get(v___x_2674_, v_alts_2664_, v___x_2675_);
lean_dec_ref(v_alts_2664_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_params_2677_; lean_object* v_code_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2729_; 
v_params_2677_ = lean_ctor_get(v___x_2676_, 1);
v_code_2678_ = lean_ctor_get(v___x_2676_, 2);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v___x_2676_, 0);
lean_dec(v_unused_2730_);
v___x_2680_ = v___x_2676_;
v_isShared_2681_ = v_isSharedCheck_2729_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_code_2678_);
lean_inc(v_params_2677_);
lean_dec(v___x_2676_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2729_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2673_, v_params_2677_, v_a_2659_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v_fvarId_2686_; lean_object* v_binderName_2687_; lean_object* v_lctx_2688_; lean_object* v_nextIdx_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2720_; 
lean_dec_ref_known(v___x_2682_, 1);
v___x_2683_ = lean_st_ref_take(v_a_2659_);
v___x_2684_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2685_ = lean_array_get(v___x_2684_, v_params_2677_, v___x_2675_);
lean_dec_ref(v_params_2677_);
v_fvarId_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_fvarId_2686_);
v_binderName_2687_ = lean_ctor_get(v___x_2685_, 1);
lean_inc(v_binderName_2687_);
lean_dec(v___x_2685_);
v_lctx_2688_ = lean_ctor_get(v___x_2683_, 0);
v_nextIdx_2689_ = lean_ctor_get(v___x_2683_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2691_ = v___x_2683_;
v_isShared_2692_ = v_isSharedCheck_2720_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_nextIdx_2689_);
lean_inc(v_lctx_2688_);
lean_dec(v___x_2683_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2720_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2693_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2695_, 0, v_discr_2663_);
v___x_2696_ = lean_mk_empty_array_with_capacity(v___x_2669_);
v___x_2697_ = lean_array_push(v___x_2696_, v___x_2695_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 3);
lean_ctor_set(v___x_2680_, 2, v___x_2697_);
lean_ctor_set(v___x_2680_, 1, v___x_2694_);
lean_ctor_set(v___x_2680_, 0, v___x_2693_);
v___x_2699_ = v___x_2680_;
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
v___x_2707_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2678_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
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
lean_del_object(v___x_2680_);
lean_dec_ref(v_code_2678_);
lean_dec_ref(v_params_2677_);
lean_del_object(v___x_2666_);
lean_dec(v_discr_2663_);
v_a_2721_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2682_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2682_);
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
lean_dec(v___x_2676_);
lean_del_object(v___x_2666_);
lean_dec(v_discr_2663_);
v___x_2731_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2732_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2731_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2732_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2737_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2738_ = lean_unsigned_to_nat(2u);
v___x_2739_ = lean_unsigned_to_nat(323u);
v___x_2740_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2741_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2742_ = l_mkPanicMessageWithDecl(v___x_2741_, v___x_2740_, v___x_2739_, v___x_2738_, v___x_2737_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2746_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2747_ = lean_unsigned_to_nat(34u);
v___x_2748_ = lean_unsigned_to_nat(324u);
v___x_2749_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2750_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2751_ = l_mkPanicMessageWithDecl(v___x_2750_, v___x_2749_, v___x_2748_, v___x_2747_, v___x_2746_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_){
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
v___x_2767_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2768_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2767_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
return v___x_2768_;
}
else
{
uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = 0;
v___x_2770_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_array_get(v___x_2770_, v_alts_2760_, v___x_2771_);
lean_dec_ref(v_alts_2760_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_params_2773_; lean_object* v_code_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2825_; 
v_params_2773_ = lean_ctor_get(v___x_2772_, 1);
v_code_2774_ = lean_ctor_get(v___x_2772_, 2);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v___x_2772_, 0);
lean_dec(v_unused_2826_);
v___x_2776_ = v___x_2772_;
v_isShared_2777_ = v_isSharedCheck_2825_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_code_2774_);
lean_inc(v_params_2773_);
lean_dec(v___x_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2825_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2769_, v_params_2773_, v_a_2755_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_fvarId_2782_; lean_object* v_binderName_2783_; lean_object* v_lctx_2784_; lean_object* v_nextIdx_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref_known(v___x_2778_, 1);
v___x_2779_ = lean_st_ref_take(v_a_2755_);
v___x_2780_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2781_ = lean_array_get(v___x_2780_, v_params_2773_, v___x_2771_);
lean_dec_ref(v_params_2773_);
v_fvarId_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_fvarId_2782_);
v_binderName_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_binderName_2783_);
lean_dec(v___x_2781_);
v_lctx_2784_ = lean_ctor_get(v___x_2779_, 0);
v_nextIdx_2785_ = lean_ctor_get(v___x_2779_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2787_ = v___x_2779_;
v_isShared_2788_ = v_isSharedCheck_2816_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_nextIdx_2785_);
lean_inc(v_lctx_2784_);
lean_dec(v___x_2779_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2816_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2789_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2790_ = lean_box(0);
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_discr_2759_);
v___x_2792_ = lean_mk_empty_array_with_capacity(v___x_2765_);
v___x_2793_ = lean_array_push(v___x_2792_, v___x_2791_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 3);
lean_ctor_set(v___x_2776_, 2, v___x_2793_);
lean_ctor_set(v___x_2776_, 1, v___x_2790_);
lean_ctor_set(v___x_2776_, 0, v___x_2789_);
v___x_2795_ = v___x_2776_;
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
v___x_2803_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2774_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
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
lean_del_object(v___x_2776_);
lean_dec_ref(v_code_2774_);
lean_dec_ref(v_params_2773_);
lean_del_object(v___x_2762_);
lean_dec(v_discr_2759_);
v_a_2817_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2778_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2778_);
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
lean_dec(v___x_2772_);
lean_del_object(v___x_2762_);
lean_dec(v_discr_2759_);
v___x_2827_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2828_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2827_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
return v___x_2828_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2833_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2834_ = lean_unsigned_to_nat(2u);
v___x_2835_ = lean_unsigned_to_nat(312u);
v___x_2836_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2837_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2838_ = l_mkPanicMessageWithDecl(v___x_2837_, v___x_2836_, v___x_2835_, v___x_2834_, v___x_2833_);
return v___x_2838_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2843_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2844_ = lean_unsigned_to_nat(34u);
v___x_2845_ = lean_unsigned_to_nat(313u);
v___x_2846_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2847_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2848_ = l_mkPanicMessageWithDecl(v___x_2847_, v___x_2846_, v___x_2845_, v___x_2844_, v___x_2843_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_){
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
v___x_2864_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2865_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2864_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
return v___x_2865_;
}
else
{
uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = 0;
v___x_2867_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2868_ = lean_unsigned_to_nat(0u);
v___x_2869_ = lean_array_get(v___x_2867_, v_alts_2857_, v___x_2868_);
lean_dec_ref(v_alts_2857_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_params_2870_; lean_object* v_code_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2922_; 
v_params_2870_ = lean_ctor_get(v___x_2869_, 1);
v_code_2871_ = lean_ctor_get(v___x_2869_, 2);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2922_ == 0)
{
lean_object* v_unused_2923_; 
v_unused_2923_ = lean_ctor_get(v___x_2869_, 0);
lean_dec(v_unused_2923_);
v___x_2873_ = v___x_2869_;
v_isShared_2874_ = v_isSharedCheck_2922_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_code_2871_);
lean_inc(v_params_2870_);
lean_dec(v___x_2869_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2922_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2866_, v_params_2870_, v_a_2852_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v_fvarId_2879_; lean_object* v_binderName_2880_; lean_object* v_lctx_2881_; lean_object* v_nextIdx_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref_known(v___x_2875_, 1);
v___x_2876_ = lean_st_ref_take(v_a_2852_);
v___x_2877_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2878_ = lean_array_get(v___x_2877_, v_params_2870_, v___x_2868_);
lean_dec_ref(v_params_2870_);
v_fvarId_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_fvarId_2879_);
v_binderName_2880_ = lean_ctor_get(v___x_2878_, 1);
lean_inc(v_binderName_2880_);
lean_dec(v___x_2878_);
v_lctx_2881_ = lean_ctor_get(v___x_2876_, 0);
v_nextIdx_2882_ = lean_ctor_get(v___x_2876_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2884_ = v___x_2876_;
v_isShared_2885_ = v_isSharedCheck_2913_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_nextIdx_2882_);
lean_inc(v_lctx_2881_);
lean_dec(v___x_2876_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2913_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2886_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_discr_2856_);
v___x_2889_ = lean_mk_empty_array_with_capacity(v___x_2862_);
v___x_2890_ = lean_array_push(v___x_2889_, v___x_2888_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set_tag(v___x_2873_, 3);
lean_ctor_set(v___x_2873_, 2, v___x_2890_);
lean_ctor_set(v___x_2873_, 1, v___x_2887_);
lean_ctor_set(v___x_2873_, 0, v___x_2886_);
v___x_2892_ = v___x_2873_;
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
v___x_2900_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2871_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
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
lean_del_object(v___x_2873_);
lean_dec_ref(v_code_2871_);
lean_dec_ref(v_params_2870_);
lean_del_object(v___x_2859_);
lean_dec(v_discr_2856_);
v_a_2914_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2875_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2875_);
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
lean_dec(v___x_2869_);
lean_del_object(v___x_2859_);
lean_dec(v_discr_2856_);
v___x_2924_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2925_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2924_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
return v___x_2925_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2930_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2931_ = lean_unsigned_to_nat(2u);
v___x_2932_ = lean_unsigned_to_nat(301u);
v___x_2933_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2934_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2935_ = l_mkPanicMessageWithDecl(v___x_2934_, v___x_2933_, v___x_2932_, v___x_2931_, v___x_2930_);
return v___x_2935_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2940_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_2941_ = lean_unsigned_to_nat(34u);
v___x_2942_ = lean_unsigned_to_nat(302u);
v___x_2943_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2944_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_2945_ = l_mkPanicMessageWithDecl(v___x_2944_, v___x_2943_, v___x_2942_, v___x_2941_, v___x_2940_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_discr_2953_; lean_object* v_alts_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3023_; 
v_discr_2953_ = lean_ctor_get(v_c_2946_, 2);
v_alts_2954_ = lean_ctor_get(v_c_2946_, 3);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_c_2946_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; lean_object* v_unused_3025_; 
v_unused_3024_ = lean_ctor_get(v_c_2946_, 1);
lean_dec(v_unused_3024_);
v_unused_3025_ = lean_ctor_get(v_c_2946_, 0);
lean_dec(v_unused_3025_);
v___x_2956_ = v_c_2946_;
v_isShared_2957_ = v_isSharedCheck_3023_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_alts_2954_);
lean_inc(v_discr_2953_);
lean_dec(v_c_2946_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3023_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v___x_2958_ = lean_array_get_size(v_alts_2954_);
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_dec_eq(v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
lean_del_object(v___x_2956_);
lean_dec_ref(v_alts_2954_);
lean_dec(v_discr_2953_);
v___x_2961_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2962_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2961_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
return v___x_2962_;
}
else
{
uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2963_ = 0;
v___x_2964_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = lean_array_get(v___x_2964_, v_alts_2954_, v___x_2965_);
lean_dec_ref(v_alts_2954_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_params_2967_; lean_object* v_code_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3019_; 
v_params_2967_ = lean_ctor_get(v___x_2966_, 1);
v_code_2968_ = lean_ctor_get(v___x_2966_, 2);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3019_ == 0)
{
lean_object* v_unused_3020_; 
v_unused_3020_ = lean_ctor_get(v___x_2966_, 0);
lean_dec(v_unused_3020_);
v___x_2970_ = v___x_2966_;
v_isShared_2971_ = v_isSharedCheck_3019_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_code_2968_);
lean_inc(v_params_2967_);
lean_dec(v___x_2966_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3019_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2963_, v_params_2967_, v_a_2949_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_fvarId_2976_; lean_object* v_binderName_2977_; lean_object* v_lctx_2978_; lean_object* v_nextIdx_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref_known(v___x_2972_, 1);
v___x_2973_ = lean_st_ref_take(v_a_2949_);
v___x_2974_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_2975_ = lean_array_get(v___x_2974_, v_params_2967_, v___x_2965_);
lean_dec_ref(v_params_2967_);
v_fvarId_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_fvarId_2976_);
v_binderName_2977_ = lean_ctor_get(v___x_2975_, 1);
lean_inc(v_binderName_2977_);
lean_dec(v___x_2975_);
v_lctx_2978_ = lean_ctor_get(v___x_2973_, 0);
v_nextIdx_2979_ = lean_ctor_get(v___x_2973_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2981_ = v___x_2973_;
v_isShared_2982_ = v_isSharedCheck_3010_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_nextIdx_2979_);
lean_inc(v_lctx_2978_);
lean_dec(v___x_2973_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3010_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v___x_2983_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_discr_2953_);
v___x_2986_ = lean_mk_empty_array_with_capacity(v___x_2959_);
v___x_2987_ = lean_array_push(v___x_2986_, v___x_2985_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set_tag(v___x_2970_, 3);
lean_ctor_set(v___x_2970_, 2, v___x_2987_);
lean_ctor_set(v___x_2970_, 1, v___x_2984_);
lean_ctor_set(v___x_2970_, 0, v___x_2983_);
v___x_2989_ = v___x_2970_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v___x_2987_);
v___x_2989_ = v_reuseFailAlloc_3009_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2990_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 3, v___x_2989_);
lean_ctor_set(v___x_2956_, 2, v___x_2990_);
lean_ctor_set(v___x_2956_, 1, v_binderName_2977_);
lean_ctor_set(v___x_2956_, 0, v_fvarId_2976_);
v___x_2992_ = v___x_2956_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fvarId_2976_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_binderName_2977_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v___x_2989_);
v___x_2992_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
lean_inc_ref(v___x_2992_);
v___x_2993_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2963_, v_lctx_2978_, v___x_2992_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2993_);
v___x_2995_ = v___x_2981_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v_nextIdx_2979_);
v___x_2995_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_st_ref_put(v_a_2949_, v___x_2995_);
v___x_2997_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2968_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3006_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3006_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_2992_);
lean_ctor_set(v___x_3002_, 1, v_a_2998_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3002_);
v___x_3004_ = v___x_3000_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
else
{
lean_dec_ref(v___x_2992_);
return v___x_2997_;
}
}
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_del_object(v___x_2970_);
lean_dec_ref(v_code_2968_);
lean_dec_ref(v_params_2967_);
lean_del_object(v___x_2956_);
lean_dec(v_discr_2953_);
v_a_3011_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2972_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2972_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
lean_dec(v___x_2966_);
lean_del_object(v___x_2956_);
lean_dec(v_discr_2953_);
v___x_3021_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_3022_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3021_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
return v___x_3022_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3027_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_3028_ = lean_unsigned_to_nat(2u);
v___x_3029_ = lean_unsigned_to_nat(289u);
v___x_3030_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_3031_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3032_ = l_mkPanicMessageWithDecl(v___x_3031_, v___x_3030_, v___x_3029_, v___x_3028_, v___x_3027_);
return v___x_3032_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3036_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3037_ = lean_unsigned_to_nat(34u);
v___x_3038_ = lean_unsigned_to_nat(290u);
v___x_3039_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_3040_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3041_ = l_mkPanicMessageWithDecl(v___x_3040_, v___x_3039_, v___x_3038_, v___x_3037_, v___x_3036_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_){
_start:
{
lean_object* v_discr_3049_; lean_object* v_alts_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3119_; 
v_discr_3049_ = lean_ctor_get(v_c_3042_, 2);
v_alts_3050_ = lean_ctor_get(v_c_3042_, 3);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_c_3042_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; lean_object* v_unused_3121_; 
v_unused_3120_ = lean_ctor_get(v_c_3042_, 1);
lean_dec(v_unused_3120_);
v_unused_3121_ = lean_ctor_get(v_c_3042_, 0);
lean_dec(v_unused_3121_);
v___x_3052_ = v_c_3042_;
v_isShared_3053_ = v_isSharedCheck_3119_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_alts_3050_);
lean_inc(v_discr_3049_);
lean_dec(v_c_3042_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3119_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3054_ = lean_array_get_size(v_alts_3050_);
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = lean_nat_dec_eq(v___x_3054_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_del_object(v___x_3052_);
lean_dec_ref(v_alts_3050_);
lean_dec(v_discr_3049_);
v___x_3057_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_3058_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3057_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
return v___x_3058_;
}
else
{
uint8_t v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3059_ = 0;
v___x_3060_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = lean_array_get(v___x_3060_, v_alts_3050_, v___x_3061_);
lean_dec_ref(v_alts_3050_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_params_3063_; lean_object* v_code_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3115_; 
v_params_3063_ = lean_ctor_get(v___x_3062_, 1);
v_code_3064_ = lean_ctor_get(v___x_3062_, 2);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3062_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3062_, 0);
lean_dec(v_unused_3116_);
v___x_3066_ = v___x_3062_;
v_isShared_3067_ = v_isSharedCheck_3115_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_code_3064_);
lean_inc(v_params_3063_);
lean_dec(v___x_3062_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3115_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3059_, v_params_3063_, v_a_3045_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_fvarId_3072_; lean_object* v_binderName_3073_; lean_object* v_lctx_3074_; lean_object* v_nextIdx_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref_known(v___x_3068_, 1);
v___x_3069_ = lean_st_ref_take(v_a_3045_);
v___x_3070_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3071_ = lean_array_get(v___x_3070_, v_params_3063_, v___x_3061_);
lean_dec_ref(v_params_3063_);
v_fvarId_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_fvarId_3072_);
v_binderName_3073_ = lean_ctor_get(v___x_3071_, 1);
lean_inc(v_binderName_3073_);
lean_dec(v___x_3071_);
v_lctx_3074_ = lean_ctor_get(v___x_3069_, 0);
v_nextIdx_3075_ = lean_ctor_get(v___x_3069_, 1);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3077_ = v___x_3069_;
v_isShared_3078_ = v_isSharedCheck_3106_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_nextIdx_3075_);
lean_inc(v_lctx_3074_);
lean_dec(v___x_3069_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3106_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3079_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_discr_3049_);
v___x_3082_ = lean_mk_empty_array_with_capacity(v___x_3055_);
v___x_3083_ = lean_array_push(v___x_3082_, v___x_3081_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set_tag(v___x_3066_, 3);
lean_ctor_set(v___x_3066_, 2, v___x_3083_);
lean_ctor_set(v___x_3066_, 1, v___x_3080_);
lean_ctor_set(v___x_3066_, 0, v___x_3079_);
v___x_3085_ = v___x_3066_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
v___x_3086_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 3, v___x_3085_);
lean_ctor_set(v___x_3052_, 2, v___x_3086_);
lean_ctor_set(v___x_3052_, 1, v_binderName_3073_);
lean_ctor_set(v___x_3052_, 0, v_fvarId_3072_);
v___x_3088_ = v___x_3052_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_fvarId_3072_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_binderName_3073_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v___x_3086_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v___x_3085_);
v___x_3088_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
lean_inc_ref(v___x_3088_);
v___x_3089_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3059_, v_lctx_3074_, v___x_3088_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3089_);
v___x_3091_ = v___x_3077_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3089_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_nextIdx_3075_);
v___x_3091_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_st_ref_put(v_a_3045_, v___x_3091_);
v___x_3093_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3064_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3088_);
lean_ctor_set(v___x_3098_, 1, v_a_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
else
{
lean_dec_ref(v___x_3088_);
return v___x_3093_;
}
}
}
}
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_del_object(v___x_3066_);
lean_dec_ref(v_code_3064_);
lean_dec_ref(v_params_3063_);
lean_del_object(v___x_3052_);
lean_dec(v_discr_3049_);
v_a_3107_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3068_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3068_);
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
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec(v___x_3062_);
lean_del_object(v___x_3052_);
lean_dec(v_discr_3049_);
v___x_3117_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_3118_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3117_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_);
return v___x_3118_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3123_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_3124_ = lean_unsigned_to_nat(2u);
v___x_3125_ = lean_unsigned_to_nat(277u);
v___x_3126_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_3127_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3128_ = l_mkPanicMessageWithDecl(v___x_3127_, v___x_3126_, v___x_3125_, v___x_3124_, v___x_3123_);
return v___x_3128_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3133_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3134_ = lean_unsigned_to_nat(34u);
v___x_3135_ = lean_unsigned_to_nat(278u);
v___x_3136_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_3137_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3138_ = l_mkPanicMessageWithDecl(v___x_3137_, v___x_3136_, v___x_3135_, v___x_3134_, v___x_3133_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v_discr_3146_; lean_object* v_alts_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3216_; 
v_discr_3146_ = lean_ctor_get(v_c_3139_, 2);
v_alts_3147_ = lean_ctor_get(v_c_3139_, 3);
v_isSharedCheck_3216_ = !lean_is_exclusive(v_c_3139_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; lean_object* v_unused_3218_; 
v_unused_3217_ = lean_ctor_get(v_c_3139_, 1);
lean_dec(v_unused_3217_);
v_unused_3218_ = lean_ctor_get(v_c_3139_, 0);
lean_dec(v_unused_3218_);
v___x_3149_ = v_c_3139_;
v_isShared_3150_ = v_isSharedCheck_3216_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_alts_3147_);
lean_inc(v_discr_3146_);
lean_dec(v_c_3139_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3216_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = lean_array_get_size(v_alts_3147_);
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_nat_dec_eq(v___x_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_del_object(v___x_3149_);
lean_dec_ref(v_alts_3147_);
lean_dec(v_discr_3146_);
v___x_3154_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_3155_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3154_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
return v___x_3155_;
}
else
{
uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3156_ = 0;
v___x_3157_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3158_ = lean_unsigned_to_nat(0u);
v___x_3159_ = lean_array_get(v___x_3157_, v_alts_3147_, v___x_3158_);
lean_dec_ref(v_alts_3147_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_params_3160_; lean_object* v_code_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3212_; 
v_params_3160_ = lean_ctor_get(v___x_3159_, 1);
v_code_3161_ = lean_ctor_get(v___x_3159_, 2);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3159_, 0);
lean_dec(v_unused_3213_);
v___x_3163_ = v___x_3159_;
v_isShared_3164_ = v_isSharedCheck_3212_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_code_3161_);
lean_inc(v_params_3160_);
lean_dec(v___x_3159_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3212_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3156_, v_params_3160_, v_a_3142_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v_fvarId_3169_; lean_object* v_binderName_3170_; lean_object* v_lctx_3171_; lean_object* v_nextIdx_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref_known(v___x_3165_, 1);
v___x_3166_ = lean_st_ref_take(v_a_3142_);
v___x_3167_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3168_ = lean_array_get(v___x_3167_, v_params_3160_, v___x_3158_);
lean_dec_ref(v_params_3160_);
v_fvarId_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_fvarId_3169_);
v_binderName_3170_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_binderName_3170_);
lean_dec(v___x_3168_);
v_lctx_3171_ = lean_ctor_get(v___x_3166_, 0);
v_nextIdx_3172_ = lean_ctor_get(v___x_3166_, 1);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3174_ = v___x_3166_;
v_isShared_3175_ = v_isSharedCheck_3203_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_nextIdx_3172_);
lean_inc(v_lctx_3171_);
lean_dec(v___x_3166_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3203_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3176_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3178_, 0, v_discr_3146_);
v___x_3179_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_3180_ = lean_array_push(v___x_3179_, v___x_3178_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 3);
lean_ctor_set(v___x_3163_, 2, v___x_3180_);
lean_ctor_set(v___x_3163_, 1, v___x_3177_);
lean_ctor_set(v___x_3163_, 0, v___x_3176_);
v___x_3182_ = v___x_3163_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3183_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 3, v___x_3182_);
lean_ctor_set(v___x_3149_, 2, v___x_3183_);
lean_ctor_set(v___x_3149_, 1, v_binderName_3170_);
lean_ctor_set(v___x_3149_, 0, v_fvarId_3169_);
v___x_3185_ = v___x_3149_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_fvarId_3169_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_binderName_3170_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3201_, 3, v___x_3182_);
v___x_3185_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
lean_inc_ref(v___x_3185_);
v___x_3186_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3156_, v_lctx_3171_, v___x_3185_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3186_);
v___x_3188_ = v___x_3174_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_nextIdx_3172_);
v___x_3188_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_st_ref_put(v_a_3142_, v___x_3188_);
v___x_3190_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3161_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3197_; 
v___x_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3185_);
lean_ctor_set(v___x_3195_, 1, v_a_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_dec_ref(v___x_3185_);
return v___x_3190_;
}
}
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_del_object(v___x_3163_);
lean_dec_ref(v_code_3161_);
lean_dec_ref(v_params_3160_);
lean_del_object(v___x_3149_);
lean_dec(v_discr_3146_);
v_a_3204_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3165_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3165_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec(v___x_3159_);
lean_del_object(v___x_3149_);
lean_dec(v_discr_3146_);
v___x_3214_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_3215_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3214_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
return v___x_3215_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3220_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_3221_ = lean_unsigned_to_nat(2u);
v___x_3222_ = lean_unsigned_to_nat(266u);
v___x_3223_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3224_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3225_ = l_mkPanicMessageWithDecl(v___x_3224_, v___x_3223_, v___x_3222_, v___x_3221_, v___x_3220_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3227_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__30));
v___x_3228_ = lean_unsigned_to_nat(34u);
v___x_3229_ = lean_unsigned_to_nat(267u);
v___x_3230_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_3231_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__28));
v___x_3232_ = l_mkPanicMessageWithDecl(v___x_3231_, v___x_3230_, v___x_3229_, v___x_3228_, v___x_3227_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_3233_, lean_object* v_uintName_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_discr_3241_; lean_object* v_alts_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3312_; 
v_discr_3241_ = lean_ctor_get(v_c_3233_, 2);
v_alts_3242_ = lean_ctor_get(v_c_3233_, 3);
v_isSharedCheck_3312_ = !lean_is_exclusive(v_c_3233_);
if (v_isSharedCheck_3312_ == 0)
{
lean_object* v_unused_3313_; lean_object* v_unused_3314_; 
v_unused_3313_ = lean_ctor_get(v_c_3233_, 1);
lean_dec(v_unused_3313_);
v_unused_3314_ = lean_ctor_get(v_c_3233_, 0);
lean_dec(v_unused_3314_);
v___x_3244_ = v_c_3233_;
v_isShared_3245_ = v_isSharedCheck_3312_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_alts_3242_);
lean_inc(v_discr_3241_);
lean_dec(v_c_3233_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3312_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v___x_3246_ = lean_array_get_size(v_alts_3242_);
v___x_3247_ = lean_unsigned_to_nat(1u);
v___x_3248_ = lean_nat_dec_eq(v___x_3246_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
lean_del_object(v___x_3244_);
lean_dec_ref(v_alts_3242_);
lean_dec(v_discr_3241_);
lean_dec(v_uintName_3234_);
v___x_3249_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_3250_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3249_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3250_;
}
else
{
uint8_t v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3251_ = 0;
v___x_3252_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_3253_ = lean_unsigned_to_nat(0u);
v___x_3254_ = lean_array_get(v___x_3252_, v_alts_3242_, v___x_3253_);
lean_dec_ref(v_alts_3242_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_params_3255_; lean_object* v_code_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3308_; 
v_params_3255_ = lean_ctor_get(v___x_3254_, 1);
v_code_3256_ = lean_ctor_get(v___x_3254_, 2);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; 
v_unused_3309_ = lean_ctor_get(v___x_3254_, 0);
lean_dec(v_unused_3309_);
v___x_3258_ = v___x_3254_;
v_isShared_3259_ = v_isSharedCheck_3308_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_code_3256_);
lean_inc(v_params_3255_);
lean_dec(v___x_3254_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3308_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3251_, v_params_3255_, v_a_3237_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v_fvarId_3264_; lean_object* v_binderName_3265_; lean_object* v_lctx_3266_; lean_object* v_nextIdx_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3299_; 
lean_dec_ref_known(v___x_3260_, 1);
v___x_3261_ = lean_st_ref_take(v_a_3237_);
v___x_3262_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3263_ = lean_array_get(v___x_3262_, v_params_3255_, v___x_3253_);
lean_dec_ref(v_params_3255_);
v_fvarId_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_fvarId_3264_);
v_binderName_3265_ = lean_ctor_get(v___x_3263_, 1);
lean_inc(v_binderName_3265_);
lean_dec(v___x_3263_);
v_lctx_3266_ = lean_ctor_get(v___x_3261_, 0);
v_nextIdx_3267_ = lean_ctor_get(v___x_3261_, 1);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3269_ = v___x_3261_;
v_isShared_3270_ = v_isSharedCheck_3299_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_nextIdx_3267_);
lean_inc(v_lctx_3266_);
lean_dec(v___x_3261_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3299_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3271_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3));
v___x_3272_ = l_Lean_Name_str___override(v_uintName_3234_, v___x_3271_);
v___x_3273_ = lean_box(0);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v_discr_3241_);
v___x_3275_ = lean_mk_empty_array_with_capacity(v___x_3247_);
v___x_3276_ = lean_array_push(v___x_3275_, v___x_3274_);
if (v_isShared_3259_ == 0)
{
lean_ctor_set_tag(v___x_3258_, 3);
lean_ctor_set(v___x_3258_, 2, v___x_3276_);
lean_ctor_set(v___x_3258_, 1, v___x_3273_);
lean_ctor_set(v___x_3258_, 0, v___x_3272_);
v___x_3278_ = v___x_3258_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = l_Lean_Compiler_LCNF_anyExpr;
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 3, v___x_3278_);
lean_ctor_set(v___x_3244_, 2, v___x_3279_);
lean_ctor_set(v___x_3244_, 1, v_binderName_3265_);
lean_ctor_set(v___x_3244_, 0, v_fvarId_3264_);
v___x_3281_ = v___x_3244_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_fvarId_3264_);
lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_binderName_3265_);
lean_ctor_set(v_reuseFailAlloc_3297_, 2, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3297_, 3, v___x_3278_);
v___x_3281_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
lean_inc_ref(v___x_3281_);
v___x_3282_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3251_, v_lctx_3266_, v___x_3281_);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3282_);
v___x_3284_ = v___x_3269_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_nextIdx_3267_);
v___x_3284_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_st_ref_put(v_a_3237_, v___x_3284_);
v___x_3286_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3256_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3295_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3295_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3281_);
lean_ctor_set(v___x_3291_, 1, v_a_3287_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3291_);
v___x_3293_ = v___x_3289_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
else
{
lean_dec_ref(v___x_3281_);
return v___x_3286_;
}
}
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_del_object(v___x_3258_);
lean_dec_ref(v_code_3256_);
lean_dec_ref(v_params_3255_);
lean_del_object(v___x_3244_);
lean_dec(v_discr_3241_);
lean_dec(v_uintName_3234_);
v_a_3300_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3260_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3260_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec(v___x_3254_);
lean_del_object(v___x_3244_);
lean_dec(v_discr_3241_);
lean_dec(v_uintName_3234_);
v___x_3310_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4);
v___x_3311_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3310_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3311_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3318_ = lean_box(0);
v___x_3319_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3320_ = l_Lean_mkConst(v___x_3319_, v___x_3318_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(lean_object* v___x_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_bs_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v___x_3341_; 
v___x_3341_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; 
lean_dec_ref(v___x_3331_);
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v_bs_3334_);
return v___x_3342_;
}
else
{
lean_object* v_v_3343_; lean_object* v___x_3344_; lean_object* v_bs_x27_3345_; lean_object* v_a_3347_; 
v_v_3343_ = lean_array_uget(v_bs_3334_, v_i_3333_);
v___x_3344_ = lean_unsigned_to_nat(0u);
v_bs_x27_3345_ = lean_array_uset(v_bs_3334_, v_i_3333_, v___x_3344_);
if (lean_obj_tag(v_v_3343_) == 0)
{
lean_object* v_ctorName_3352_; lean_object* v_params_3353_; lean_object* v_code_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3432_; 
v_ctorName_3352_ = lean_ctor_get(v_v_3343_, 0);
v_params_3353_ = lean_ctor_get(v_v_3343_, 1);
v_code_3354_ = lean_ctor_get(v_v_3343_, 2);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_v_3343_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3356_ = v_v_3343_;
v_isShared_3357_ = v_isSharedCheck_3432_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_code_3354_);
lean_inc(v_params_3353_);
lean_inc(v_ctorName_3352_);
lean_dec(v_v_3343_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3432_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
uint8_t v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = 0;
v___x_3359_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3358_, v_params_3353_, v___y_3337_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3360_; uint8_t v___x_3361_; 
lean_dec_ref_known(v___x_3359_, 1);
v___x_3360_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__23));
v___x_3361_ = lean_name_eq(v_ctorName_3352_, v___x_3360_);
lean_dec(v_ctorName_3352_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec_ref(v_params_3353_);
v___x_3362_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3354_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
v___x_3364_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___x_3365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 2, v_a_3363_);
lean_ctor_set(v___x_3356_, 1, v___x_3365_);
lean_ctor_set(v___x_3356_, 0, v___x_3364_);
v___x_3367_ = v___x_3356_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3364_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_a_3363_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
v_a_3347_ = v___x_3367_;
goto v___jp_3346_;
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_del_object(v___x_3356_);
lean_dec_ref(v_bs_x27_3345_);
lean_dec_ref(v___x_3331_);
v_a_3369_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3362_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3362_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v_fvarId_3379_; lean_object* v_binderName_3380_; lean_object* v_type_3381_; lean_object* v___x_3382_; 
v___x_3377_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3378_ = lean_array_get(v___x_3377_, v_params_3353_, v___x_3344_);
lean_dec_ref(v_params_3353_);
v_fvarId_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_fvarId_3379_);
v_binderName_3380_ = lean_ctor_get(v___x_3378_, 1);
lean_inc(v_binderName_3380_);
v_type_3381_ = lean_ctor_get(v___x_3378_, 2);
lean_inc_ref(v_type_3381_);
lean_dec(v___x_3378_);
v___x_3382_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3381_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v_lctx_3385_; lean_object* v_nextIdx_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3415_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = lean_st_ref_take(v___y_3337_);
v_lctx_3385_ = lean_ctor_get(v___x_3384_, 0);
v_nextIdx_3386_ = lean_ctor_get(v___x_3384_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3388_ = v___x_3384_;
v_isShared_3389_ = v_isSharedCheck_3415_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_nextIdx_3386_);
lean_inc(v_lctx_3385_);
lean_dec(v___x_3384_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3415_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3390_ = lean_box(0);
v___x_3391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___closed__1));
lean_inc_ref(v___x_3331_);
v___x_3392_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___x_3390_);
lean_ctor_set(v___x_3392_, 2, v___x_3331_);
v___x_3393_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3393_, 0, v_fvarId_3379_);
lean_ctor_set(v___x_3393_, 1, v_binderName_3380_);
lean_ctor_set(v___x_3393_, 2, v_a_3383_);
lean_ctor_set(v___x_3393_, 3, v___x_3392_);
lean_inc_ref(v___x_3393_);
v___x_3394_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3358_, v_lctx_3385_, v___x_3393_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3394_);
v___x_3396_ = v___x_3388_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_nextIdx_3386_);
v___x_3396_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = lean_st_ref_put(v___y_3337_, v___x_3396_);
v___x_3398_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3354_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3400_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___x_3401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3393_);
lean_ctor_set(v___x_3402_, 1, v_a_3399_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 2, v___x_3402_);
lean_ctor_set(v___x_3356_, 1, v___x_3401_);
lean_ctor_set(v___x_3356_, 0, v___x_3400_);
v___x_3404_ = v___x_3356_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v___x_3402_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
v_a_3347_ = v___x_3404_;
goto v___jp_3346_;
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref_known(v___x_3393_, 4);
lean_del_object(v___x_3356_);
lean_dec_ref(v_bs_x27_3345_);
lean_dec_ref(v___x_3331_);
v_a_3406_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3398_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3398_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_binderName_3380_);
lean_dec(v_fvarId_3379_);
lean_del_object(v___x_3356_);
lean_dec_ref(v_code_3354_);
lean_dec_ref(v_bs_x27_3345_);
lean_dec_ref(v___x_3331_);
v_a_3416_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3382_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3382_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_del_object(v___x_3356_);
lean_dec_ref(v_code_3354_);
lean_dec_ref(v_params_3353_);
lean_dec(v_ctorName_3352_);
lean_dec_ref(v_bs_x27_3345_);
lean_dec_ref(v___x_3331_);
v_a_3424_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3359_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3359_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
lean_object* v_code_3433_; lean_object* v___x_3434_; 
v_code_3433_ = lean_ctor_get(v_v_3343_, 0);
lean_inc_ref(v_code_3433_);
v___x_3434_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3433_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3343_, v_a_3435_);
v_a_3347_ = v___x_3436_;
goto v___jp_3346_;
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref_known(v_v_3343_, 1);
lean_dec_ref(v_bs_x27_3345_);
lean_dec_ref(v___x_3331_);
v_a_3437_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3434_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3434_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
v___jp_3346_:
{
size_t v___x_3348_; size_t v___x_3349_; lean_object* v___x_3350_; 
v___x_3348_ = ((size_t)1ULL);
v___x_3349_ = lean_usize_add(v_i_3333_, v___x_3348_);
v___x_3350_ = lean_array_uset(v_bs_x27_3345_, v_i_3333_, v_a_3347_);
v_i_3333_ = v___x_3349_;
v_bs_3334_ = v___x_3350_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(lean_object* v_c_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_resultType_3452_; lean_object* v_discr_3453_; lean_object* v_alts_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3513_; 
v_resultType_3452_ = lean_ctor_get(v_c_3445_, 1);
v_discr_3453_ = lean_ctor_get(v_c_3445_, 2);
v_alts_3454_ = lean_ctor_get(v_c_3445_, 3);
v_isSharedCheck_3513_ = !lean_is_exclusive(v_c_3445_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; 
v_unused_3514_ = lean_ctor_get(v_c_3445_, 0);
lean_dec(v_unused_3514_);
v___x_3456_ = v_c_3445_;
v_isShared_3457_ = v_isSharedCheck_3513_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_alts_3454_);
lean_inc(v_discr_3453_);
lean_inc(v_resultType_3452_);
lean_dec(v_c_3445_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3513_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3452_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; uint8_t v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = 0;
v___x_3461_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__1));
v___x_3462_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2);
v___x_3465_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__4));
v___x_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3466_, 0, v_discr_3453_);
v___x_3467_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__5);
v___x_3468_ = lean_array_push(v___x_3467_, v___x_3466_);
lean_inc_ref(v___x_3468_);
v___x_3469_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3465_);
lean_ctor_set(v___x_3469_, 1, v___x_3463_);
lean_ctor_set(v___x_3469_, 2, v___x_3468_);
v___x_3470_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3460_, v___x_3461_, v___x_3464_, v___x_3469_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; size_t v_sz_3472_; size_t v___x_3473_; lean_object* v___x_3474_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v_sz_3472_ = lean_array_size(v_alts_3454_);
v___x_3473_ = ((size_t)0ULL);
v___x_3474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(v___x_3468_, v_sz_3472_, v___x_3473_, v_alts_3454_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3488_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3488_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3488_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v_fvarId_3479_; lean_object* v___x_3481_; 
v_fvarId_3479_ = lean_ctor_get(v_a_3471_, 0);
lean_inc(v_fvarId_3479_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 3, v_a_3475_);
lean_ctor_set(v___x_3456_, 2, v_fvarId_3479_);
lean_ctor_set(v___x_3456_, 1, v_a_3459_);
lean_ctor_set(v___x_3456_, 0, v___x_3462_);
v___x_3481_ = v___x_3456_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_a_3459_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_fvarId_3479_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_a_3475_);
v___x_3481_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3482_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v_a_3471_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v___x_3483_);
v___x_3485_ = v___x_3477_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v_a_3471_);
lean_dec(v_a_3459_);
lean_del_object(v___x_3456_);
v_a_3489_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3474_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3474_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___x_3468_);
lean_dec(v_a_3459_);
lean_del_object(v___x_3456_);
lean_dec_ref(v_alts_3454_);
v_a_3497_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3470_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3470_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_del_object(v___x_3456_);
lean_dec_ref(v_alts_3454_);
lean_dec(v_discr_3453_);
v_a_3505_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3458_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3458_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_box(0);
v___x_3516_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3517_ = l_Lean_mkConst(v___x_3516_, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3524_ = lean_box(0);
v___x_3525_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3526_ = l_Lean_mkConst(v___x_3525_, v___x_3524_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(lean_object* v___x_3556_, size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_bs_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
uint8_t v___x_3566_; 
v___x_3566_ = lean_usize_dec_lt(v_i_3558_, v_sz_3557_);
if (v___x_3566_ == 0)
{
lean_object* v___x_3567_; 
lean_dec(v___x_3556_);
v___x_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_bs_3559_);
return v___x_3567_;
}
else
{
lean_object* v_v_3568_; lean_object* v___x_3569_; lean_object* v_bs_x27_3570_; lean_object* v_a_3572_; 
v_v_3568_ = lean_array_uget(v_bs_3559_, v_i_3558_);
v___x_3569_ = lean_unsigned_to_nat(0u);
v_bs_x27_3570_ = lean_array_uset(v_bs_3559_, v_i_3558_, v___x_3569_);
if (lean_obj_tag(v_v_3568_) == 0)
{
lean_object* v_ctorName_3577_; lean_object* v_params_3578_; lean_object* v_code_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3706_; 
v_ctorName_3577_ = lean_ctor_get(v_v_3568_, 0);
v_params_3578_ = lean_ctor_get(v_v_3568_, 1);
v_code_3579_ = lean_ctor_get(v_v_3568_, 2);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_v_3568_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3581_ = v_v_3568_;
v_isShared_3582_ = v_isSharedCheck_3706_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_code_3579_);
lean_inc(v_params_3578_);
lean_inc(v_ctorName_3577_);
lean_dec(v_v_3568_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3706_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
uint8_t v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3583_ = 0;
v___x_3584_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3585_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3583_, v_params_3578_, v___y_3562_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
lean_dec_ref_known(v___x_3585_, 1);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3588_ = lean_array_get(v___x_3584_, v_params_3578_, v___x_3569_);
lean_dec_ref(v_params_3578_);
v___x_3589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__1));
v___x_3590_ = lean_name_eq(v_ctorName_3577_, v___x_3589_);
lean_dec(v_ctorName_3577_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v_fvarId_3592_; lean_object* v_binderName_3593_; lean_object* v_lctx_3594_; lean_object* v_nextIdx_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3626_; 
v___x_3591_ = lean_st_ref_take(v___y_3562_);
v_fvarId_3592_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_fvarId_3592_);
v_binderName_3593_ = lean_ctor_get(v___x_3588_, 1);
lean_inc(v_binderName_3593_);
lean_dec(v___x_3588_);
v_lctx_3594_ = lean_ctor_get(v___x_3591_, 0);
v_nextIdx_3595_ = lean_ctor_get(v___x_3591_, 1);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3597_ = v___x_3591_;
v_isShared_3598_ = v_isSharedCheck_3626_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_nextIdx_3595_);
lean_inc(v_lctx_3594_);
lean_dec(v___x_3591_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3626_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3));
v___x_3600_ = lean_unsigned_to_nat(1u);
v___x_3601_ = lean_mk_empty_array_with_capacity(v___x_3600_);
lean_inc(v___x_3556_);
v___x_3602_ = lean_array_push(v___x_3601_, v___x_3556_);
v___x_3603_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3599_);
lean_ctor_set(v___x_3603_, 1, v___x_3586_);
lean_ctor_set(v___x_3603_, 2, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3604_, 0, v_fvarId_3592_);
lean_ctor_set(v___x_3604_, 1, v_binderName_3593_);
lean_ctor_set(v___x_3604_, 2, v___x_3587_);
lean_ctor_set(v___x_3604_, 3, v___x_3603_);
lean_inc_ref(v___x_3604_);
v___x_3605_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3583_, v_lctx_3594_, v___x_3604_);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3605_);
v___x_3607_ = v___x_3597_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_nextIdx_3595_);
v___x_3607_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_st_ref_put(v___y_3562_, v___x_3607_);
v___x_3609_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3579_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v_a_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3615_; 
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_a_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3611_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___x_3612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3604_);
lean_ctor_set(v___x_3613_, 1, v_a_3610_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 2, v___x_3613_);
lean_ctor_set(v___x_3581_, 1, v___x_3612_);
lean_ctor_set(v___x_3581_, 0, v___x_3611_);
v___x_3615_ = v___x_3581_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3616_, 2, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
v_a_3572_ = v___x_3615_;
goto v___jp_3571_;
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref_known(v___x_3604_, 4);
lean_del_object(v___x_3581_);
lean_dec_ref(v_bs_x27_3570_);
lean_dec(v___x_3556_);
v_a_3617_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3609_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3609_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
}
}
else
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__5));
v___x_3628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___closed__3));
v___x_3629_ = lean_unsigned_to_nat(1u);
v___x_3630_ = lean_mk_empty_array_with_capacity(v___x_3629_);
lean_inc(v___x_3556_);
v___x_3631_ = lean_array_push(v___x_3630_, v___x_3556_);
v___x_3632_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3628_);
lean_ctor_set(v___x_3632_, 1, v___x_3586_);
lean_ctor_set(v___x_3632_, 2, v___x_3631_);
v___x_3633_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3583_, v___x_3627_, v___x_3587_, v___x_3632_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v___x_3635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1));
v___x_3636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3));
v___x_3637_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3583_, v___x_3635_, v___x_3587_, v___x_3636_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_fvarId_3639_; lean_object* v_fvarId_3640_; lean_object* v___x_3641_; lean_object* v_fvarId_3642_; lean_object* v_binderName_3643_; lean_object* v_lctx_3644_; lean_object* v_nextIdx_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3681_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_fvarId_3639_ = lean_ctor_get(v_a_3634_, 0);
v_fvarId_3640_ = lean_ctor_get(v_a_3638_, 0);
v___x_3641_ = lean_st_ref_take(v___y_3562_);
v_fvarId_3642_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_fvarId_3642_);
v_binderName_3643_ = lean_ctor_get(v___x_3588_, 1);
lean_inc(v_binderName_3643_);
lean_dec(v___x_3588_);
v_lctx_3644_ = lean_ctor_get(v___x_3641_, 0);
v_nextIdx_3645_ = lean_ctor_get(v___x_3641_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3647_ = v___x_3641_;
v_isShared_3648_ = v_isSharedCheck_3681_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_nextIdx_3645_);
lean_inc(v_lctx_3644_);
lean_dec(v___x_3641_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3681_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5));
lean_inc(v_fvarId_3639_);
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v_fvarId_3639_);
lean_inc(v_fvarId_3640_);
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_fvarId_3640_);
v___x_3652_ = lean_unsigned_to_nat(2u);
v___x_3653_ = lean_mk_empty_array_with_capacity(v___x_3652_);
v___x_3654_ = lean_array_push(v___x_3653_, v___x_3650_);
v___x_3655_ = lean_array_push(v___x_3654_, v___x_3651_);
v___x_3656_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3649_);
lean_ctor_set(v___x_3656_, 1, v___x_3586_);
lean_ctor_set(v___x_3656_, 2, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3657_, 0, v_fvarId_3642_);
lean_ctor_set(v___x_3657_, 1, v_binderName_3643_);
lean_ctor_set(v___x_3657_, 2, v___x_3587_);
lean_ctor_set(v___x_3657_, 3, v___x_3656_);
lean_inc_ref(v___x_3657_);
v___x_3658_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3583_, v_lctx_3644_, v___x_3657_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 0, v___x_3658_);
v___x_3660_ = v___x_3647_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_nextIdx_3645_);
v___x_3660_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_st_ref_put(v___y_3562_, v___x_3660_);
v___x_3662_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3579_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3670_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v___x_3664_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___x_3665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3657_);
lean_ctor_set(v___x_3666_, 1, v_a_3663_);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v_a_3638_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3668_, 0, v_a_3634_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 2, v___x_3668_);
lean_ctor_set(v___x_3581_, 1, v___x_3665_);
lean_ctor_set(v___x_3581_, 0, v___x_3664_);
v___x_3670_ = v___x_3581_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3671_, 2, v___x_3668_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_a_3572_ = v___x_3670_;
goto v___jp_3571_;
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref_known(v___x_3657_, 4);
lean_dec(v_a_3638_);
lean_dec(v_a_3634_);
lean_del_object(v___x_3581_);
lean_dec_ref(v_bs_x27_3570_);
lean_dec(v___x_3556_);
v_a_3672_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3662_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3662_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
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
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_a_3634_);
lean_dec(v___x_3588_);
lean_del_object(v___x_3581_);
lean_dec_ref(v_code_3579_);
lean_dec_ref(v_bs_x27_3570_);
lean_dec(v___x_3556_);
v_a_3682_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3637_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3637_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v___x_3588_);
lean_del_object(v___x_3581_);
lean_dec_ref(v_code_3579_);
lean_dec_ref(v_bs_x27_3570_);
lean_dec(v___x_3556_);
v_a_3690_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3633_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3633_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_del_object(v___x_3581_);
lean_dec_ref(v_code_3579_);
lean_dec_ref(v_params_3578_);
lean_dec(v_ctorName_3577_);
lean_dec_ref(v_bs_x27_3570_);
lean_dec(v___x_3556_);
v_a_3698_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3585_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3585_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
else
{
lean_object* v_code_3707_; lean_object* v___x_3708_; 
v_code_3707_ = lean_ctor_get(v_v_3568_, 0);
lean_inc_ref(v_code_3707_);
v___x_3708_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3707_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; lean_object* v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3568_, v_a_3709_);
v_a_3572_ = v___x_3710_;
goto v___jp_3571_;
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec_ref_known(v_v_3568_, 1);
lean_dec_ref(v_bs_x27_3570_);
lean_dec(v___x_3556_);
v_a_3711_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3708_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3708_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
v___jp_3571_:
{
size_t v___x_3573_; size_t v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = ((size_t)1ULL);
v___x_3574_ = lean_usize_add(v_i_3558_, v___x_3573_);
v___x_3575_ = lean_array_uset(v_bs_x27_3570_, v_i_3558_, v_a_3572_);
v_i_3558_ = v___x_3574_;
v_bs_3559_ = v___x_3575_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v_resultType_3726_; lean_object* v_discr_3727_; lean_object* v_alts_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3825_; 
v_resultType_3726_ = lean_ctor_get(v_c_3719_, 1);
v_discr_3727_ = lean_ctor_get(v_c_3719_, 2);
v_alts_3728_ = lean_ctor_get(v_c_3719_, 3);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_c_3719_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v_c_3719_, 0);
lean_dec(v_unused_3826_);
v___x_3730_ = v_c_3719_;
v_isShared_3731_ = v_isSharedCheck_3825_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_alts_3728_);
lean_inc(v_discr_3727_);
lean_inc(v_resultType_3726_);
lean_dec(v_c_3719_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3825_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3726_, v_a_3723_, v_a_3724_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; uint8_t v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v___x_3734_ = 0;
v___x_3735_ = lean_box(0);
v___x_3736_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3737_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3738_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__33));
v___x_3739_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3734_, v___x_3737_, v___x_3736_, v___x_3738_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v_fvarId_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
v_fvarId_3741_ = lean_ctor_get(v_a_3740_, 0);
v___x_3742_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3743_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3744_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3741_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_fvarId_3741_);
v___x_3746_ = lean_unsigned_to_nat(1u);
v___x_3747_ = lean_mk_empty_array_with_capacity(v___x_3746_);
v___x_3748_ = lean_array_push(v___x_3747_, v___x_3745_);
v___x_3749_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3744_);
lean_ctor_set(v___x_3749_, 1, v___x_3735_);
lean_ctor_set(v___x_3749_, 2, v___x_3748_);
v___x_3750_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3734_, v___x_3742_, v___x_3743_, v___x_3749_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v_fvarId_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v_fvarId_3752_ = lean_ctor_get(v_a_3751_, 0);
v___x_3753_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3754_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3755_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2);
v___x_3756_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3757_, 0, v_discr_3727_);
lean_inc(v_fvarId_3752_);
v___x_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3758_, 0, v_fvarId_3752_);
v___x_3759_ = lean_unsigned_to_nat(2u);
v___x_3760_ = lean_mk_empty_array_with_capacity(v___x_3759_);
lean_inc_ref(v___x_3757_);
v___x_3761_ = lean_array_push(v___x_3760_, v___x_3757_);
v___x_3762_ = lean_array_push(v___x_3761_, v___x_3758_);
v___x_3763_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3756_);
lean_ctor_set(v___x_3763_, 1, v___x_3735_);
lean_ctor_set(v___x_3763_, 2, v___x_3762_);
v___x_3764_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3734_, v___x_3753_, v___x_3755_, v___x_3763_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; size_t v_sz_3766_; size_t v___x_3767_; lean_object* v___x_3768_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
v_sz_3766_ = lean_array_size(v_alts_3728_);
v___x_3767_ = ((size_t)0ULL);
v___x_3768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(v___x_3757_, v_sz_3766_, v___x_3767_, v_alts_3728_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3784_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3784_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3784_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_fvarId_3773_; lean_object* v___x_3775_; 
v_fvarId_3773_ = lean_ctor_get(v_a_3765_, 0);
lean_inc(v_fvarId_3773_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 3, v_a_3769_);
lean_ctor_set(v___x_3730_, 2, v_fvarId_3773_);
lean_ctor_set(v___x_3730_, 1, v_a_3733_);
lean_ctor_set(v___x_3730_, 0, v___x_3754_);
v___x_3775_ = v___x_3730_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3754_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_a_3733_);
lean_ctor_set(v_reuseFailAlloc_3783_, 2, v_fvarId_3773_);
lean_ctor_set(v_reuseFailAlloc_3783_, 3, v_a_3769_);
v___x_3775_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3781_; 
v___x_3776_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3777_, 0, v_a_3765_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3778_, 0, v_a_3751_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v_a_3740_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3779_);
v___x_3781_ = v___x_3771_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec(v_a_3765_);
lean_dec(v_a_3751_);
lean_dec(v_a_3740_);
lean_dec(v_a_3733_);
lean_del_object(v___x_3730_);
v_a_3785_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3768_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3768_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref_known(v___x_3757_, 1);
lean_dec(v_a_3751_);
lean_dec(v_a_3740_);
lean_dec(v_a_3733_);
lean_del_object(v___x_3730_);
lean_dec_ref(v_alts_3728_);
v_a_3793_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3764_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3764_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec(v_a_3740_);
lean_dec(v_a_3733_);
lean_del_object(v___x_3730_);
lean_dec_ref(v_alts_3728_);
lean_dec(v_discr_3727_);
v_a_3801_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3750_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3750_);
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
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec(v_a_3733_);
lean_del_object(v___x_3730_);
lean_dec_ref(v_alts_3728_);
lean_dec(v_discr_3727_);
v_a_3809_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3739_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3739_);
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
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_del_object(v___x_3730_);
lean_dec_ref(v_alts_3728_);
lean_dec(v_discr_3727_);
v_a_3817_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3732_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3732_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(lean_object* v___x_3836_, size_t v_sz_3837_, size_t v_i_3838_, lean_object* v_bs_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
uint8_t v___x_3846_; 
v___x_3846_ = lean_usize_dec_lt(v_i_3838_, v_sz_3837_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; 
lean_dec(v___x_3836_);
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_bs_3839_);
return v___x_3847_;
}
else
{
lean_object* v_v_3848_; lean_object* v___x_3849_; lean_object* v_bs_x27_3850_; lean_object* v_a_3852_; 
v_v_3848_ = lean_array_uget(v_bs_3839_, v_i_3838_);
v___x_3849_ = lean_unsigned_to_nat(0u);
v_bs_x27_3850_ = lean_array_uset(v_bs_3839_, v_i_3838_, v___x_3849_);
if (lean_obj_tag(v_v_3848_) == 0)
{
lean_object* v_ctorName_3857_; lean_object* v_params_3858_; lean_object* v_code_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3946_; 
v_ctorName_3857_ = lean_ctor_get(v_v_3848_, 0);
v_params_3858_ = lean_ctor_get(v_v_3848_, 1);
v_code_3859_ = lean_ctor_get(v_v_3848_, 2);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_v_3848_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3861_ = v_v_3848_;
v_isShared_3862_ = v_isSharedCheck_3946_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_code_3859_);
lean_inc(v_params_3858_);
lean_inc(v_ctorName_3857_);
lean_dec(v_v_3848_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3946_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
uint8_t v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = 0;
v___x_3864_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3863_, v_params_3858_, v___y_3842_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v___x_3865_; uint8_t v___x_3866_; 
lean_dec_ref_known(v___x_3864_, 1);
v___x_3865_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__18));
v___x_3866_ = lean_name_eq(v_ctorName_3857_, v___x_3865_);
lean_dec(v_ctorName_3857_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; 
lean_dec_ref(v_params_3858_);
v___x_3867_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3859_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v___x_3869_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___x_3870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 2, v_a_3868_);
lean_ctor_set(v___x_3861_, 1, v___x_3870_);
lean_ctor_set(v___x_3861_, 0, v___x_3869_);
v___x_3872_ = v___x_3861_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_a_3868_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
v_a_3852_ = v___x_3872_;
goto v___jp_3851_;
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_del_object(v___x_3861_);
lean_dec_ref(v_bs_x27_3850_);
lean_dec(v___x_3836_);
v_a_3874_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3867_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3867_);
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
else
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3884_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_argsToMonoRedArg_spec__0___redArg___closed__0);
v___x_3885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__1));
v___x_3886_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3));
v___x_3887_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3863_, v___x_3885_, v___x_3883_, v___x_3886_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v_fvarId_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v_fvarId_3892_; lean_object* v_binderName_3893_; lean_object* v_lctx_3894_; lean_object* v_nextIdx_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3929_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
v_fvarId_3889_ = lean_ctor_get(v_a_3888_, 0);
v___x_3890_ = lean_st_ref_take(v___y_3842_);
v___x_3891_ = lean_array_get(v___x_3884_, v_params_3858_, v___x_3849_);
lean_dec_ref(v_params_3858_);
v_fvarId_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_fvarId_3892_);
v_binderName_3893_ = lean_ctor_get(v___x_3891_, 1);
lean_inc(v_binderName_3893_);
lean_dec(v___x_3891_);
v_lctx_3894_ = lean_ctor_get(v___x_3890_, 0);
v_nextIdx_3895_ = lean_ctor_get(v___x_3890_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3897_ = v___x_3890_;
v_isShared_3898_ = v_isSharedCheck_3929_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_nextIdx_3895_);
lean_inc(v_lctx_3894_);
lean_dec(v___x_3890_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3929_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__5));
lean_inc(v_fvarId_3889_);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v_fvarId_3889_);
v___x_3901_ = lean_unsigned_to_nat(2u);
v___x_3902_ = lean_mk_empty_array_with_capacity(v___x_3901_);
lean_inc(v___x_3836_);
v___x_3903_ = lean_array_push(v___x_3902_, v___x_3836_);
v___x_3904_ = lean_array_push(v___x_3903_, v___x_3900_);
v___x_3905_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3899_);
lean_ctor_set(v___x_3905_, 1, v___x_3882_);
lean_ctor_set(v___x_3905_, 2, v___x_3904_);
v___x_3906_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3906_, 0, v_fvarId_3892_);
lean_ctor_set(v___x_3906_, 1, v_binderName_3893_);
lean_ctor_set(v___x_3906_, 2, v___x_3883_);
lean_ctor_set(v___x_3906_, 3, v___x_3905_);
lean_inc_ref(v___x_3906_);
v___x_3907_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3863_, v_lctx_3894_, v___x_3906_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3907_);
v___x_3909_ = v___x_3897_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_nextIdx_3895_);
v___x_3909_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_st_ref_put(v___y_3842_, v___x_3909_);
v___x_3911_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3859_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___x_3914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3906_);
lean_ctor_set(v___x_3915_, 1, v_a_3912_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v_a_3888_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 2, v___x_3916_);
lean_ctor_set(v___x_3861_, 1, v___x_3914_);
lean_ctor_set(v___x_3861_, 0, v___x_3913_);
v___x_3918_ = v___x_3861_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3913_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v_a_3852_ = v___x_3918_;
goto v___jp_3851_;
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref_known(v___x_3906_, 4);
lean_dec(v_a_3888_);
lean_del_object(v___x_3861_);
lean_dec_ref(v_bs_x27_3850_);
lean_dec(v___x_3836_);
v_a_3920_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3911_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3911_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_del_object(v___x_3861_);
lean_dec_ref(v_code_3859_);
lean_dec_ref(v_params_3858_);
lean_dec_ref(v_bs_x27_3850_);
lean_dec(v___x_3836_);
v_a_3930_ = lean_ctor_get(v___x_3887_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3887_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3887_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_del_object(v___x_3861_);
lean_dec_ref(v_code_3859_);
lean_dec_ref(v_params_3858_);
lean_dec(v_ctorName_3857_);
lean_dec_ref(v_bs_x27_3850_);
lean_dec(v___x_3836_);
v_a_3938_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3864_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3864_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
else
{
lean_object* v_code_3947_; lean_object* v___x_3948_; 
v_code_3947_ = lean_ctor_get(v_v_3848_, 0);
lean_inc_ref(v_code_3947_);
v___x_3948_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3947_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v___x_3950_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc(v_a_3949_);
lean_dec_ref_known(v___x_3948_, 1);
v___x_3950_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3848_, v_a_3949_);
v_a_3852_ = v___x_3950_;
goto v___jp_3851_;
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec_ref_known(v_v_3848_, 1);
lean_dec_ref(v_bs_x27_3850_);
lean_dec(v___x_3836_);
v_a_3951_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3948_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3948_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
v___jp_3851_:
{
size_t v___x_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = ((size_t)1ULL);
v___x_3854_ = lean_usize_add(v_i_3838_, v___x_3853_);
v___x_3855_ = lean_array_uset(v_bs_x27_3850_, v_i_3838_, v_a_3852_);
v_i_3838_ = v___x_3854_;
v_bs_3839_ = v___x_3855_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_resultType_3966_; lean_object* v_discr_3967_; lean_object* v_alts_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4045_; 
v_resultType_3966_ = lean_ctor_get(v_c_3959_, 1);
v_discr_3967_ = lean_ctor_get(v_c_3959_, 2);
v_alts_3968_ = lean_ctor_get(v_c_3959_, 3);
v_isSharedCheck_4045_ = !lean_is_exclusive(v_c_3959_);
if (v_isSharedCheck_4045_ == 0)
{
lean_object* v_unused_4046_; 
v_unused_4046_ = lean_ctor_get(v_c_3959_, 0);
lean_dec(v_unused_4046_);
v___x_3970_ = v_c_3959_;
v_isShared_3971_ = v_isSharedCheck_4045_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_alts_3968_);
lean_inc(v_discr_3967_);
lean_inc(v_resultType_3966_);
lean_dec(v_c_3959_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4045_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3966_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; uint8_t v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = 0;
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3977_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3978_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__33));
v___x_3979_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3974_, v___x_3977_, v___x_3976_, v___x_3978_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v_fvarId_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
v_fvarId_3981_ = lean_ctor_get(v_a_3980_, 0);
v___x_3982_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3983_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
v___x_3984_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___closed__2);
v___x_3985_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3986_, 0, v_discr_3967_);
lean_inc(v_fvarId_3981_);
v___x_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3987_, 0, v_fvarId_3981_);
v___x_3988_ = lean_unsigned_to_nat(2u);
v___x_3989_ = lean_mk_empty_array_with_capacity(v___x_3988_);
lean_inc_ref(v___x_3986_);
v___x_3990_ = lean_array_push(v___x_3989_, v___x_3986_);
v___x_3991_ = lean_array_push(v___x_3990_, v___x_3987_);
v___x_3992_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3985_);
lean_ctor_set(v___x_3992_, 1, v___x_3975_);
lean_ctor_set(v___x_3992_, 2, v___x_3991_);
v___x_3993_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3974_, v___x_3982_, v___x_3984_, v___x_3992_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; size_t v_sz_3995_; size_t v___x_3996_; lean_object* v___x_3997_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3993_, 1);
v_sz_3995_ = lean_array_size(v_alts_3968_);
v___x_3996_ = ((size_t)0ULL);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(v___x_3986_, v_sz_3995_, v___x_3996_, v_alts_3968_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4012_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4012_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4012_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v_fvarId_4002_; lean_object* v___x_4004_; 
v_fvarId_4002_ = lean_ctor_get(v_a_3994_, 0);
lean_inc(v_fvarId_4002_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 3, v_a_3998_);
lean_ctor_set(v___x_3970_, 2, v_fvarId_4002_);
lean_ctor_set(v___x_3970_, 1, v_a_3973_);
lean_ctor_set(v___x_3970_, 0, v___x_3983_);
v___x_4004_ = v___x_3970_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_3983_);
lean_ctor_set(v_reuseFailAlloc_4011_, 1, v_a_3973_);
lean_ctor_set(v_reuseFailAlloc_4011_, 2, v_fvarId_4002_);
lean_ctor_set(v_reuseFailAlloc_4011_, 3, v_a_3998_);
v___x_4004_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4009_; 
v___x_4005_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v_a_3994_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v_a_3980_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
if (v_isShared_4001_ == 0)
{
lean_ctor_set(v___x_4000_, 0, v___x_4007_);
v___x_4009_ = v___x_4000_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
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
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v_a_3994_);
lean_dec(v_a_3980_);
lean_dec(v_a_3973_);
lean_del_object(v___x_3970_);
v_a_4013_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3997_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3997_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec_ref_known(v___x_3986_, 1);
lean_dec(v_a_3980_);
lean_dec(v_a_3973_);
lean_del_object(v___x_3970_);
lean_dec_ref(v_alts_3968_);
v_a_4021_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_3993_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_3993_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec(v_a_3973_);
lean_del_object(v___x_3970_);
lean_dec_ref(v_alts_3968_);
lean_dec(v_discr_3967_);
v_a_4029_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_3979_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_3979_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_del_object(v___x_3970_);
lean_dec_ref(v_alts_3968_);
lean_dec(v_discr_3967_);
v_a_4037_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_3972_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_3972_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v___y_4061_; lean_object* v___y_4062_; uint8_t v___y_4063_; lean_object* v___y_4068_; lean_object* v___y_4069_; uint8_t v___y_4070_; lean_object* v_decl_4075_; lean_object* v_k_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4122_; lean_object* v___y_4123_; uint8_t v___y_4124_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; 
switch(lean_obj_tag(v_code_4053_))
{
case 0:
{
lean_object* v_decl_4136_; lean_object* v_k_4137_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v_value_4162_; 
v_decl_4136_ = lean_ctor_get(v_code_4053_, 0);
v_k_4137_ = lean_ctor_get(v_code_4053_, 1);
v_value_4162_ = lean_ctor_get(v_decl_4136_, 3);
lean_inc(v_value_4162_);
if (lean_obj_tag(v_value_4162_) == 3)
{
lean_object* v_declName_4163_; 
v_declName_4163_ = lean_ctor_get(v_value_4162_, 0);
lean_inc(v_declName_4163_);
if (lean_obj_tag(v_declName_4163_) == 1)
{
lean_object* v_pre_4164_; 
v_pre_4164_ = lean_ctor_get(v_declName_4163_, 0);
lean_inc(v_pre_4164_);
if (lean_obj_tag(v_pre_4164_) == 1)
{
lean_object* v_pre_4165_; 
v_pre_4165_ = lean_ctor_get(v_pre_4164_, 0);
if (lean_obj_tag(v_pre_4165_) == 0)
{
lean_object* v_type_4166_; lean_object* v_args_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4237_; 
v_type_4166_ = lean_ctor_get(v_decl_4136_, 2);
v_args_4167_ = lean_ctor_get(v_value_4162_, 2);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_value_4162_);
if (v_isSharedCheck_4237_ == 0)
{
lean_object* v_unused_4238_; lean_object* v_unused_4239_; 
v_unused_4238_ = lean_ctor_get(v_value_4162_, 1);
lean_dec(v_unused_4238_);
v_unused_4239_ = lean_ctor_get(v_value_4162_, 0);
lean_dec(v_unused_4239_);
v___x_4169_ = v_value_4162_;
v_isShared_4170_ = v_isSharedCheck_4237_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_args_4167_);
lean_dec(v_value_4162_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4237_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v_str_4171_; lean_object* v_str_4172_; lean_object* v___x_4173_; uint8_t v___x_4174_; 
v_str_4171_ = lean_ctor_get(v_declName_4163_, 1);
lean_inc_ref(v_str_4171_);
lean_dec_ref_known(v_declName_4163_, 2);
v_str_4172_ = lean_ctor_get(v_pre_4164_, 1);
lean_inc_ref(v_str_4172_);
lean_dec_ref_known(v_pre_4164_, 2);
v___x_4173_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__14));
v___x_4174_ = lean_string_dec_eq(v_str_4172_, v___x_4173_);
lean_dec_ref(v_str_4172_);
if (v___x_4174_ == 0)
{
lean_dec_ref(v_str_4171_);
lean_del_object(v___x_4169_);
lean_dec_ref(v_args_4167_);
v___y_4139_ = v_a_4054_;
v___y_4140_ = v_a_4055_;
v___y_4141_ = v_a_4056_;
v___y_4142_ = v_a_4057_;
v___y_4143_ = v_a_4058_;
goto v___jp_4138_;
}
else
{
lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4175_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__17));
v___x_4176_ = lean_string_dec_eq(v_str_4171_, v___x_4175_);
lean_dec_ref(v_str_4171_);
if (v___x_4176_ == 0)
{
lean_del_object(v___x_4169_);
lean_dec_ref(v_args_4167_);
v___y_4139_ = v_a_4054_;
v___y_4140_ = v_a_4055_;
v___y_4141_ = v_a_4056_;
v___y_4142_ = v_a_4057_;
v___y_4143_ = v_a_4058_;
goto v___jp_4138_;
}
else
{
lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4234_; 
lean_inc_ref(v_type_4166_);
lean_inc_ref(v_k_4137_);
lean_inc_ref(v_decl_4136_);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_code_4053_);
if (v_isSharedCheck_4234_ == 0)
{
lean_object* v_unused_4235_; lean_object* v_unused_4236_; 
v_unused_4235_ = lean_ctor_get(v_code_4053_, 1);
lean_dec(v_unused_4235_);
v_unused_4236_ = lean_ctor_get(v_code_4053_, 0);
lean_dec(v_unused_4236_);
v___x_4178_ = v_code_4053_;
v_isShared_4179_ = v_isSharedCheck_4234_;
goto v_resetjp_4177_;
}
else
{
lean_dec(v_code_4053_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4234_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v___x_4180_ = lean_array_get_size(v_args_4167_);
v___x_4181_ = lean_unsigned_to_nat(1u);
v___x_4182_ = lean_nat_dec_eq(v___x_4180_, v___x_4181_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_del_object(v___x_4178_);
lean_del_object(v___x_4169_);
lean_dec_ref(v_args_4167_);
lean_dec_ref(v_type_4166_);
lean_dec_ref(v_k_4137_);
lean_dec_ref(v_decl_4136_);
v___x_4183_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_4184_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_4183_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4184_;
}
else
{
uint8_t v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4185_ = 0;
v___x_4186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___closed__3));
v___x_4187_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_4188_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_4185_, v___x_4186_, v___x_4187_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v_fvarId_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4201_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v_fvarId_4190_ = lean_ctor_get(v_a_4189_, 0);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = lean_array_fget(v_args_4167_, v___x_4191_);
lean_dec_ref(v_args_4167_);
v___x_4193_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_4194_ = lean_box(0);
lean_inc(v_fvarId_4190_);
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v_fvarId_4190_);
v___x_4196_ = lean_unsigned_to_nat(2u);
v___x_4197_ = lean_mk_empty_array_with_capacity(v___x_4196_);
v___x_4198_ = lean_array_push(v___x_4197_, v___x_4192_);
v___x_4199_ = lean_array_push(v___x_4198_, v___x_4195_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 2, v___x_4199_);
lean_ctor_set(v___x_4169_, 1, v___x_4194_);
lean_ctor_set(v___x_4169_, 0, v___x_4193_);
v___x_4201_ = v___x_4169_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4225_, 1, v___x_4194_);
lean_ctor_set(v_reuseFailAlloc_4225_, 2, v___x_4199_);
v___x_4201_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
lean_object* v___x_4202_; 
v___x_4202_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_4185_, v_decl_4136_, v_type_4166_, v___x_4201_, v_a_4056_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_4137_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4216_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4216_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4216_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 1, v_a_4205_);
lean_ctor_set(v___x_4178_, 0, v_a_4203_);
v___x_4210_ = v___x_4178_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4203_);
lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v_a_4189_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4211_);
v___x_4213_ = v___x_4207_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_dec(v_a_4203_);
lean_dec(v_a_4189_);
lean_del_object(v___x_4178_);
return v___x_4204_;
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_a_4189_);
lean_del_object(v___x_4178_);
lean_dec_ref(v_k_4137_);
v_a_4217_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4202_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4202_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_del_object(v___x_4178_);
lean_del_object(v___x_4169_);
lean_dec_ref(v_args_4167_);
lean_dec_ref(v_type_4166_);
lean_dec_ref(v_k_4137_);
lean_dec_ref(v_decl_4136_);
v_a_4226_ = lean_ctor_get(v___x_4188_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4188_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4188_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4188_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
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
lean_dec_ref_known(v_pre_4164_, 2);
lean_dec_ref_known(v_declName_4163_, 2);
lean_dec_ref_known(v_value_4162_, 3);
v___y_4139_ = v_a_4054_;
v___y_4140_ = v_a_4055_;
v___y_4141_ = v_a_4056_;
v___y_4142_ = v_a_4057_;
v___y_4143_ = v_a_4058_;
goto v___jp_4138_;
}
}
else
{
lean_dec(v_pre_4164_);
lean_dec_ref_known(v_declName_4163_, 2);
lean_dec_ref_known(v_value_4162_, 3);
v___y_4139_ = v_a_4054_;
v___y_4140_ = v_a_4055_;
v___y_4141_ = v_a_4056_;
v___y_4142_ = v_a_4057_;
v___y_4143_ = v_a_4058_;
goto v___jp_4138_;
}
}
else
{
lean_dec(v_declName_4163_);
lean_dec_ref_known(v_value_4162_, 3);
v___y_4139_ = v_a_4054_;
v___y_4140_ = v_a_4055_;
v___y_4141_ = v_a_4056_;
v___y_4142_ = v_a_4057_;
v___y_4143_ = v_a_4058_;
goto v___jp_4138_;
}
}
else
{
lean_dec(v_value_4162_);
v___y_4139_ = v_a_4054_;
v___y_4140_ = v_a_4055_;
v___y_4141_ = v_a_4056_;
v___y_4142_ = v_a_4057_;
v___y_4143_ = v_a_4058_;
goto v___jp_4138_;
}
v___jp_4138_:
{
lean_object* v___x_4144_; 
lean_inc_ref(v_decl_4136_);
v___x_4144_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_4136_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4146_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 1);
lean_inc_ref(v_k_4137_);
v___x_4146_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_4137_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; size_t v___x_4148_; size_t v___x_4149_; uint8_t v___x_4150_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4146_, 1);
v___x_4148_ = lean_ptr_addr(v_k_4137_);
v___x_4149_ = lean_ptr_addr(v_a_4147_);
v___x_4150_ = lean_usize_dec_eq(v___x_4148_, v___x_4149_);
if (v___x_4150_ == 0)
{
v___y_4122_ = v_a_4145_;
v___y_4123_ = v_a_4147_;
v___y_4124_ = v___x_4150_;
goto v___jp_4121_;
}
else
{
size_t v___x_4151_; size_t v___x_4152_; uint8_t v___x_4153_; 
v___x_4151_ = lean_ptr_addr(v_decl_4136_);
v___x_4152_ = lean_ptr_addr(v_a_4145_);
v___x_4153_ = lean_usize_dec_eq(v___x_4151_, v___x_4152_);
v___y_4122_ = v_a_4145_;
v___y_4123_ = v_a_4147_;
v___y_4124_ = v___x_4153_;
goto v___jp_4121_;
}
}
else
{
lean_dec(v_a_4145_);
lean_dec_ref_known(v_code_4053_, 2);
return v___x_4146_;
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec_ref_known(v_code_4053_, 2);
v_a_4154_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4144_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4144_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_4240_; lean_object* v_args_4241_; size_t v_sz_4242_; size_t v___x_4243_; lean_object* v___x_4244_; 
v_fvarId_4240_ = lean_ctor_get(v_code_4053_, 0);
v_args_4241_ = lean_ctor_get(v_code_4053_, 1);
v_sz_4242_ = lean_array_size(v_args_4241_);
v___x_4243_ = ((size_t)0ULL);
lean_inc_ref(v_args_4241_);
v___x_4244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_4242_, v___x_4243_, v_args_4241_, v_a_4054_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v_a_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4270_; 
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4247_ = v___x_4244_;
v_isShared_4248_ = v_isSharedCheck_4270_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_a_4245_);
lean_dec(v___x_4244_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4270_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
uint8_t v___y_4250_; uint8_t v___x_4266_; 
v___x_4266_ = l_Lean_instBEqFVarId_beq(v_fvarId_4240_, v_fvarId_4240_);
if (v___x_4266_ == 0)
{
v___y_4250_ = v___x_4266_;
goto v___jp_4249_;
}
else
{
size_t v___x_4267_; size_t v___x_4268_; uint8_t v___x_4269_; 
v___x_4267_ = lean_ptr_addr(v_args_4241_);
v___x_4268_ = lean_ptr_addr(v_a_4245_);
v___x_4269_ = lean_usize_dec_eq(v___x_4267_, v___x_4268_);
v___y_4250_ = v___x_4269_;
goto v___jp_4249_;
}
v___jp_4249_:
{
if (v___y_4250_ == 0)
{
lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4260_; 
lean_inc(v_fvarId_4240_);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_code_4053_);
if (v_isSharedCheck_4260_ == 0)
{
lean_object* v_unused_4261_; lean_object* v_unused_4262_; 
v_unused_4261_ = lean_ctor_get(v_code_4053_, 1);
lean_dec(v_unused_4261_);
v_unused_4262_ = lean_ctor_get(v_code_4053_, 0);
lean_dec(v_unused_4262_);
v___x_4252_ = v_code_4053_;
v_isShared_4253_ = v_isSharedCheck_4260_;
goto v_resetjp_4251_;
}
else
{
lean_dec(v_code_4053_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4260_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 1, v_a_4245_);
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_fvarId_4240_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_a_4245_);
v___x_4255_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
lean_object* v___x_4257_; 
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v___x_4255_);
v___x_4257_ = v___x_4247_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v___x_4264_; 
lean_dec(v_a_4245_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set(v___x_4247_, 0, v_code_4053_);
v___x_4264_ = v___x_4247_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_code_4053_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref_known(v_code_4053_, 2);
v_a_4271_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4244_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4244_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
case 4:
{
lean_object* v_cases_4279_; lean_object* v___x_4280_; lean_object* v_typeName_4281_; lean_object* v_resultType_4282_; lean_object* v_discr_4283_; lean_object* v_alts_4284_; lean_object* v___y_4286_; lean_object* v___y_4287_; uint8_t v___y_4288_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4319_; lean_object* v___y_4320_; uint8_t v___y_4321_; lean_object* v_env_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v_cases_4279_ = lean_ctor_get(v_code_4053_, 0);
v___x_4280_ = lean_st_ref_get(v_a_4058_);
v_typeName_4281_ = lean_ctor_get(v_cases_4279_, 0);
v_resultType_4282_ = lean_ctor_get(v_cases_4279_, 1);
v_discr_4283_ = lean_ctor_get(v_cases_4279_, 2);
v_alts_4284_ = lean_ctor_get(v_cases_4279_, 3);
v_env_4419_ = lean_ctor_get(v___x_4280_, 0);
lean_inc_ref(v_env_4419_);
lean_dec(v___x_4280_);
v___x_4420_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__25));
v___x_4421_ = lean_name_eq(v_typeName_4281_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_dec_ref(v_env_4419_);
goto v___jp_4324_;
}
else
{
lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4422_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__27));
v___x_4423_ = l_Lean_Environment_contains(v_env_4419_, v___x_4422_, v___x_4421_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4424_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4424_;
}
else
{
goto v___jp_4324_;
}
}
v___jp_4285_:
{
size_t v_sz_4289_; size_t v___x_4290_; lean_object* v___x_4291_; 
v_sz_4289_ = lean_array_size(v_alts_4284_);
v___x_4290_ = ((size_t)0ULL);
v___x_4291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___y_4287_, v___y_4288_, v_sz_4289_, v___x_4290_, v_alts_4284_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4303_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4303_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4303_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_4297_ = l_Lean_Name_append(v_typeName_4281_, v___x_4296_);
v___x_4298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
lean_ctor_set(v___x_4298_, 1, v___y_4286_);
lean_ctor_set(v___x_4298_, 2, v_discr_4283_);
lean_ctor_set(v___x_4298_, 3, v_a_4292_);
v___x_4299_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
if (v_isShared_4295_ == 0)
{
lean_ctor_set(v___x_4294_, 0, v___x_4299_);
v___x_4301_ = v___x_4294_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v___x_4299_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v___y_4286_);
lean_dec(v_discr_4283_);
lean_dec(v_typeName_4281_);
v_a_4304_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4291_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4291_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
v___jp_4312_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4315_, 0, v_typeName_4281_);
lean_ctor_set(v___x_4315_, 1, v___y_4313_);
lean_ctor_set(v___x_4315_, 2, v_discr_4283_);
lean_ctor_set(v___x_4315_, 3, v___y_4314_);
v___x_4316_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
v___x_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
return v___x_4317_;
}
v___jp_4318_:
{
if (v___y_4321_ == 0)
{
lean_inc(v_discr_4283_);
lean_inc(v_typeName_4281_);
lean_dec_ref_known(v_code_4053_, 1);
v___y_4313_ = v___y_4319_;
v___y_4314_ = v___y_4320_;
goto v___jp_4312_;
}
else
{
uint8_t v___x_4322_; 
v___x_4322_ = l_Lean_instBEqFVarId_beq(v_discr_4283_, v_discr_4283_);
if (v___x_4322_ == 0)
{
lean_inc(v_discr_4283_);
lean_inc(v_typeName_4281_);
lean_dec_ref_known(v_code_4053_, 1);
v___y_4313_ = v___y_4319_;
v___y_4314_ = v___y_4320_;
goto v___jp_4312_;
}
else
{
lean_object* v___x_4323_; 
lean_dec_ref(v___y_4320_);
lean_dec_ref(v___y_4319_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v_code_4053_);
return v___x_4323_;
}
}
}
v___jp_4324_:
{
lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4325_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_4326_ = lean_name_eq(v_typeName_4281_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; uint8_t v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_4328_ = lean_name_eq(v_typeName_4281_, v___x_4327_);
if (v___x_4328_ == 0)
{
lean_object* v___x_4329_; uint8_t v___x_4330_; 
v___x_4329_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__8));
v___x_4330_ = lean_name_eq(v_typeName_4281_, v___x_4329_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4331_; uint8_t v___x_4332_; 
v___x_4331_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__10));
v___x_4332_ = lean_name_eq(v_typeName_4281_, v___x_4331_);
if (v___x_4332_ == 0)
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__12));
v___x_4334_ = lean_name_eq(v_typeName_4281_, v___x_4333_);
if (v___x_4334_ == 0)
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__14));
v___x_4336_ = lean_name_eq(v_typeName_4281_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_4338_ = lean_name_eq(v_typeName_4281_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_4340_ = lean_name_eq(v_typeName_4281_, v___x_4339_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_4342_ = lean_name_eq(v_typeName_4281_, v___x_4341_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4343_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_4344_ = lean_name_eq(v_typeName_4281_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_4346_ = lean_name_eq(v_typeName_4281_, v___x_4345_);
if (v___x_4346_ == 0)
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_4348_ = lean_name_eq(v_typeName_4281_, v___x_4347_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_4350_ = lean_name_eq(v_typeName_4281_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_4352_ = lean_name_eq(v_typeName_4281_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; uint8_t v___x_4354_; 
v___x_4353_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__24));
v___x_4354_ = lean_name_eq(v_typeName_4281_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
lean_inc(v_typeName_4281_);
v___x_4355_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_4281_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
if (lean_obj_tag(v_a_4356_) == 1)
{
lean_object* v_val_4357_; lean_object* v___x_4358_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v_val_4357_ = lean_ctor_get(v_a_4356_, 0);
lean_inc(v_val_4357_);
lean_dec_ref_known(v_a_4356_, 1);
v___x_4358_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_4357_, v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec(v_val_4357_);
return v___x_4358_;
}
else
{
lean_object* v___x_4359_; 
lean_dec(v_a_4356_);
lean_inc_ref(v_resultType_4282_);
v___x_4359_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_4282_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; lean_object* v_env_4362_; lean_object* v___x_4363_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v___x_4361_ = lean_st_ref_get(v_a_4058_);
v_env_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc_ref_n(v_env_4362_, 2);
lean_dec(v___x_4361_);
lean_inc(v_typeName_4281_);
v___x_4363_ = l_Lean_Environment_find_x3f(v_env_4362_, v_typeName_4281_, v___x_4354_);
if (lean_obj_tag(v___x_4363_) == 1)
{
lean_object* v_val_4364_; 
v_val_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_val_4364_);
lean_dec_ref_known(v___x_4363_, 1);
if (lean_obj_tag(v_val_4364_) == 5)
{
lean_object* v_val_4365_; lean_object* v_toConstantVal_4366_; lean_object* v_name_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v_val_4365_ = lean_ctor_get(v_val_4364_, 0);
lean_inc_ref(v_val_4365_);
lean_dec_ref_known(v_val_4364_, 1);
v_toConstantVal_4366_ = lean_ctor_get(v_val_4365_, 0);
lean_inc_ref(v_toConstantVal_4366_);
lean_dec_ref(v_val_4365_);
v_name_4367_ = lean_ctor_get(v_toConstantVal_4366_, 0);
lean_inc(v_name_4367_);
lean_dec_ref(v_toConstantVal_4366_);
v___x_4368_ = l_Lean_mkCasesOnName(v_name_4367_);
lean_inc_ref(v_env_4362_);
v___x_4369_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_4362_, v___x_4368_);
if (lean_obj_tag(v___x_4369_) == 0)
{
if (v___x_4354_ == 0)
{
size_t v_sz_4370_; size_t v___x_4371_; lean_object* v___x_4372_; 
lean_dec_ref(v_env_4362_);
v_sz_4370_ = lean_array_size(v_alts_4284_);
v___x_4371_ = ((size_t)0ULL);
lean_inc_ref(v_alts_4284_);
v___x_4372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_4370_, v___x_4371_, v_alts_4284_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; size_t v___x_4374_; size_t v___x_4375_; uint8_t v___x_4376_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4372_, 1);
v___x_4374_ = lean_ptr_addr(v_alts_4284_);
v___x_4375_ = lean_ptr_addr(v_a_4373_);
v___x_4376_ = lean_usize_dec_eq(v___x_4374_, v___x_4375_);
if (v___x_4376_ == 0)
{
v___y_4319_ = v_a_4360_;
v___y_4320_ = v_a_4373_;
v___y_4321_ = v___x_4376_;
goto v___jp_4318_;
}
else
{
size_t v___x_4377_; size_t v___x_4378_; uint8_t v___x_4379_; 
v___x_4377_ = lean_ptr_addr(v_resultType_4282_);
v___x_4378_ = lean_ptr_addr(v_a_4360_);
v___x_4379_ = lean_usize_dec_eq(v___x_4377_, v___x_4378_);
v___y_4319_ = v_a_4360_;
v___y_4320_ = v_a_4373_;
v___y_4321_ = v___x_4379_;
goto v___jp_4318_;
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4360_);
lean_dec_ref_known(v_code_4053_, 1);
v_a_4380_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4372_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4372_);
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
else
{
lean_inc_ref(v_alts_4284_);
lean_inc(v_discr_4283_);
lean_inc(v_typeName_4281_);
lean_dec_ref_known(v_code_4053_, 1);
v___y_4286_ = v_a_4360_;
v___y_4287_ = v_env_4362_;
v___y_4288_ = v___x_4354_;
goto v___jp_4285_;
}
}
else
{
lean_inc_ref(v_alts_4284_);
lean_inc(v_discr_4283_);
lean_inc(v_typeName_4281_);
lean_dec_ref_known(v___x_4369_, 1);
lean_dec_ref_known(v_code_4053_, 1);
v___y_4286_ = v_a_4360_;
v___y_4287_ = v_env_4362_;
v___y_4288_ = v___x_4354_;
goto v___jp_4285_;
}
}
else
{
lean_dec(v_val_4364_);
lean_dec_ref(v_env_4362_);
lean_dec(v_a_4360_);
lean_dec_ref_known(v_code_4053_, 1);
v___y_4129_ = v_a_4054_;
v___y_4130_ = v_a_4055_;
v___y_4131_ = v_a_4056_;
v___y_4132_ = v_a_4057_;
v___y_4133_ = v_a_4058_;
goto v___jp_4128_;
}
}
else
{
lean_dec(v___x_4363_);
lean_dec_ref(v_env_4362_);
lean_dec(v_a_4360_);
lean_dec_ref_known(v_code_4053_, 1);
v___y_4129_ = v_a_4054_;
v___y_4130_ = v_a_4055_;
v___y_4131_ = v_a_4056_;
v___y_4132_ = v_a_4057_;
v___y_4133_ = v_a_4058_;
goto v___jp_4128_;
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec_ref_known(v_code_4053_, 1);
v_a_4388_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4359_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4359_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec_ref_known(v_code_4053_, 1);
v_a_4396_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4355_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4355_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
else
{
lean_object* v___x_4404_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4404_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4404_;
}
}
else
{
lean_object* v___x_4405_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4405_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
lean_dec_ref(v_cases_4279_);
return v___x_4405_;
}
}
else
{
lean_object* v___x_4406_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4406_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4406_;
}
}
else
{
lean_object* v___x_4407_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4407_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4407_;
}
}
else
{
lean_object* v___x_4408_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4408_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4408_;
}
}
else
{
lean_object* v___x_4409_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4409_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4409_;
}
}
else
{
lean_object* v___x_4410_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4410_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4410_;
}
}
else
{
lean_object* v___x_4411_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4411_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4411_;
}
}
else
{
lean_object* v___x_4412_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4412_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4279_, v___x_4337_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4412_;
}
}
else
{
lean_object* v___x_4413_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4413_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4279_, v___x_4335_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4413_;
}
}
else
{
lean_object* v___x_4414_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4414_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4279_, v___x_4333_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4414_;
}
}
else
{
lean_object* v___x_4415_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4415_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_4279_, v___x_4331_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4415_;
}
}
else
{
lean_object* v___x_4416_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4416_ = l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4416_;
}
}
else
{
lean_object* v___x_4417_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4417_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4417_;
}
}
else
{
lean_object* v___x_4418_; 
lean_inc_ref(v_cases_4279_);
lean_dec_ref_known(v_code_4053_, 1);
v___x_4418_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_4279_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_, v_a_4058_);
return v___x_4418_;
}
}
}
case 5:
{
lean_object* v___x_4425_; 
v___x_4425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4425_, 0, v_code_4053_);
return v___x_4425_;
}
case 6:
{
lean_object* v_type_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4450_; 
v_type_4426_ = lean_ctor_get(v_code_4053_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v_code_4053_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4428_ = v_code_4053_;
v_isShared_4429_ = v_isSharedCheck_4450_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_type_4426_);
lean_dec(v_code_4053_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4450_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4426_, v_a_4057_, v_a_4058_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4441_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4441_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4441_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v_a_4431_);
v___x_4436_ = v___x_4428_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4438_; 
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4436_);
v___x_4438_ = v___x_4433_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_del_object(v___x_4428_);
v_a_4442_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4430_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4430_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
}
default: 
{
lean_object* v_decl_4451_; lean_object* v_k_4452_; 
v_decl_4451_ = lean_ctor_get(v_code_4053_, 0);
v_k_4452_ = lean_ctor_get(v_code_4053_, 1);
lean_inc_ref(v_k_4452_);
lean_inc_ref(v_decl_4451_);
v_decl_4075_ = v_decl_4451_;
v_k_4076_ = v_k_4452_;
v___y_4077_ = v_a_4054_;
v___y_4078_ = v_a_4055_;
v___y_4079_ = v_a_4056_;
v___y_4080_ = v_a_4057_;
v___y_4081_ = v_a_4058_;
goto v___jp_4074_;
}
}
v___jp_4060_:
{
if (v___y_4063_ == 0)
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_dec_ref(v_code_4053_);
v___x_4064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4064_, 0, v___y_4061_);
lean_ctor_set(v___x_4064_, 1, v___y_4062_);
v___x_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
return v___x_4065_;
}
else
{
lean_object* v___x_4066_; 
lean_dec_ref(v___y_4062_);
lean_dec_ref(v___y_4061_);
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_code_4053_);
return v___x_4066_;
}
}
v___jp_4067_:
{
if (v___y_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_dec_ref(v_code_4053_);
v___x_4071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___y_4068_);
lean_ctor_set(v___x_4071_, 1, v___y_4069_);
v___x_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4071_);
return v___x_4072_;
}
else
{
lean_object* v___x_4073_; 
lean_dec_ref(v___y_4069_);
lean_dec_ref(v___y_4068_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v_code_4053_);
return v___x_4073_;
}
}
v___jp_4074_:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_4075_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
if (lean_obj_tag(v___x_4084_) == 0)
{
switch(lean_obj_tag(v_code_4053_))
{
case 1:
{
lean_object* v_a_4085_; lean_object* v_decl_4086_; lean_object* v_k_4087_; size_t v___x_4088_; size_t v___x_4089_; uint8_t v___x_4090_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v_decl_4086_ = lean_ctor_get(v_code_4053_, 0);
v_k_4087_ = lean_ctor_get(v_code_4053_, 1);
v___x_4088_ = lean_ptr_addr(v_k_4087_);
v___x_4089_ = lean_ptr_addr(v_a_4085_);
v___x_4090_ = lean_usize_dec_eq(v___x_4088_, v___x_4089_);
if (v___x_4090_ == 0)
{
v___y_4061_ = v_a_4083_;
v___y_4062_ = v_a_4085_;
v___y_4063_ = v___x_4090_;
goto v___jp_4060_;
}
else
{
size_t v___x_4091_; size_t v___x_4092_; uint8_t v___x_4093_; 
v___x_4091_ = lean_ptr_addr(v_decl_4086_);
v___x_4092_ = lean_ptr_addr(v_a_4083_);
v___x_4093_ = lean_usize_dec_eq(v___x_4091_, v___x_4092_);
v___y_4061_ = v_a_4083_;
v___y_4062_ = v_a_4085_;
v___y_4063_ = v___x_4093_;
goto v___jp_4060_;
}
}
case 2:
{
lean_object* v_a_4094_; lean_object* v_decl_4095_; lean_object* v_k_4096_; size_t v___x_4097_; size_t v___x_4098_; uint8_t v___x_4099_; 
v_a_4094_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4084_, 1);
v_decl_4095_ = lean_ctor_get(v_code_4053_, 0);
v_k_4096_ = lean_ctor_get(v_code_4053_, 1);
v___x_4097_ = lean_ptr_addr(v_k_4096_);
v___x_4098_ = lean_ptr_addr(v_a_4094_);
v___x_4099_ = lean_usize_dec_eq(v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
v___y_4068_ = v_a_4083_;
v___y_4069_ = v_a_4094_;
v___y_4070_ = v___x_4099_;
goto v___jp_4067_;
}
else
{
size_t v___x_4100_; size_t v___x_4101_; uint8_t v___x_4102_; 
v___x_4100_ = lean_ptr_addr(v_decl_4095_);
v___x_4101_ = lean_ptr_addr(v_a_4083_);
v___x_4102_ = lean_usize_dec_eq(v___x_4100_, v___x_4101_);
v___y_4068_ = v_a_4083_;
v___y_4069_ = v_a_4094_;
v___y_4070_ = v___x_4102_;
goto v___jp_4067_;
}
}
default: 
{
lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v_a_4083_);
lean_dec_ref(v_code_4053_);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4111_ == 0)
{
lean_object* v_unused_4112_; 
v_unused_4112_ = lean_ctor_get(v___x_4084_, 0);
lean_dec(v_unused_4112_);
v___x_4104_ = v___x_4084_;
v_isShared_4105_ = v_isSharedCheck_4111_;
goto v_resetjp_4103_;
}
else
{
lean_dec(v___x_4084_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4111_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4109_; 
v___x_4106_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__2, &l_Lean_Compiler_LCNF_Code_toMono___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2);
v___x_4107_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_4106_);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4107_);
v___x_4109_ = v___x_4104_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
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
lean_dec(v_a_4083_);
lean_dec_ref(v_code_4053_);
return v___x_4084_;
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec_ref(v_k_4076_);
lean_dec_ref(v_code_4053_);
v_a_4113_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4082_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4082_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
v___jp_4121_:
{
if (v___y_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
lean_dec_ref(v_code_4053_);
v___x_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___y_4122_);
lean_ctor_set(v___x_4125_, 1, v___y_4123_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
else
{
lean_object* v___x_4127_; 
lean_dec_ref(v___y_4123_);
lean_dec_ref(v___y_4122_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v_code_4053_);
return v___x_4127_;
}
}
v___jp_4128_:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_4135_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_4134_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(size_t v_sz_4453_, size_t v_i_4454_, lean_object* v_bs_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_usize_dec_lt(v_i_4454_, v_sz_4453_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_bs_4455_);
return v___x_4463_;
}
else
{
lean_object* v_v_4464_; lean_object* v___x_4465_; lean_object* v_bs_x27_4466_; lean_object* v_a_4468_; 
v_v_4464_ = lean_array_uget(v_bs_4455_, v_i_4454_);
v___x_4465_ = lean_unsigned_to_nat(0u);
v_bs_x27_4466_ = lean_array_uset(v_bs_4455_, v_i_4454_, v___x_4465_);
if (lean_obj_tag(v_v_4464_) == 0)
{
lean_object* v_ctorName_4473_; lean_object* v_params_4474_; lean_object* v_code_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4509_; 
v_ctorName_4473_ = lean_ctor_get(v_v_4464_, 0);
v_params_4474_ = lean_ctor_get(v_v_4464_, 1);
v_code_4475_ = lean_ctor_get(v_v_4464_, 2);
v_isSharedCheck_4509_ = !lean_is_exclusive(v_v_4464_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4477_ = v_v_4464_;
v_isShared_4478_ = v_isSharedCheck_4509_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_code_4475_);
lean_inc(v_params_4474_);
lean_inc(v_ctorName_4473_);
lean_dec(v_v_4464_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4509_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
uint8_t v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = 0;
v___x_4480_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_4479_, v_params_4474_, v___y_4458_);
lean_dec_ref(v_params_4474_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v___y_4482_; lean_object* v___x_4497_; uint8_t v___x_4498_; 
lean_dec_ref_known(v___x_4480_, 1);
v___x_4497_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_4498_ = lean_name_eq(v_ctorName_4473_, v___x_4497_);
lean_dec(v_ctorName_4473_);
if (v___x_4498_ == 0)
{
lean_object* v___x_4499_; 
v___x_4499_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__36));
v___y_4482_ = v___x_4499_;
goto v___jp_4481_;
}
else
{
lean_object* v___x_4500_; 
v___x_4500_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__39));
v___y_4482_ = v___x_4500_;
goto v___jp_4481_;
}
v___jp_4481_:
{
lean_object* v___x_4483_; 
v___x_4483_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4475_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; lean_object* v___x_4485_; lean_object* v___x_4487_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
v___x_4485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___closed__0));
lean_inc(v___y_4482_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 2, v_a_4484_);
lean_ctor_set(v___x_4477_, 1, v___x_4485_);
lean_ctor_set(v___x_4477_, 0, v___y_4482_);
v___x_4487_ = v___x_4477_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___y_4482_);
lean_ctor_set(v_reuseFailAlloc_4488_, 1, v___x_4485_);
lean_ctor_set(v_reuseFailAlloc_4488_, 2, v_a_4484_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
v_a_4468_ = v___x_4487_;
goto v___jp_4467_;
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_del_object(v___x_4477_);
lean_dec_ref(v_bs_x27_4466_);
v_a_4489_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4483_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4483_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_del_object(v___x_4477_);
lean_dec_ref(v_code_4475_);
lean_dec(v_ctorName_4473_);
lean_dec_ref(v_bs_x27_4466_);
v_a_4501_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4480_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4480_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
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
}
else
{
lean_object* v_code_4510_; lean_object* v___x_4511_; 
v_code_4510_ = lean_ctor_get(v_v_4464_, 0);
lean_inc_ref(v_code_4510_);
v___x_4511_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4510_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4513_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref_known(v___x_4511_, 1);
v___x_4513_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_4464_, v_a_4512_);
v_a_4468_ = v___x_4513_;
goto v___jp_4467_;
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec_ref_known(v_v_4464_, 1);
lean_dec_ref(v_bs_x27_4466_);
v_a_4514_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4511_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4511_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
v___jp_4467_:
{
size_t v___x_4469_; size_t v___x_4470_; lean_object* v___x_4471_; 
v___x_4469_ = ((size_t)1ULL);
v___x_4470_ = lean_usize_add(v_i_4454_, v___x_4469_);
v___x_4471_ = lean_array_uset(v_bs_x27_4466_, v_i_4454_, v_a_4468_);
v_i_4454_ = v___x_4470_;
v_bs_4455_ = v___x_4471_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg(lean_object* v_c_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v_resultType_4529_; lean_object* v_discr_4530_; lean_object* v_alts_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4569_; 
v_resultType_4529_ = lean_ctor_get(v_c_4522_, 1);
v_discr_4530_ = lean_ctor_get(v_c_4522_, 2);
v_alts_4531_ = lean_ctor_get(v_c_4522_, 3);
v_isSharedCheck_4569_ = !lean_is_exclusive(v_c_4522_);
if (v_isSharedCheck_4569_ == 0)
{
lean_object* v_unused_4570_; 
v_unused_4570_ = lean_ctor_get(v_c_4522_, 0);
lean_dec(v_unused_4570_);
v___x_4533_ = v_c_4522_;
v_isShared_4534_ = v_isSharedCheck_4569_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_alts_4531_);
lean_inc(v_discr_4530_);
lean_inc(v_resultType_4529_);
lean_dec(v_c_4522_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4569_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_4529_, v_a_4526_, v_a_4527_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; size_t v_sz_4537_; size_t v___x_4538_; lean_object* v___x_4539_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v_sz_4537_ = lean_array_size(v_alts_4531_);
v___x_4538_ = ((size_t)0ULL);
v___x_4539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(v_sz_4537_, v___x_4538_, v_alts_4531_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4552_; 
v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4542_ = v___x_4539_;
v_isShared_4543_ = v_isSharedCheck_4552_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4539_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4552_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4544_; lean_object* v___x_4546_; 
v___x_4544_ = ((lean_object*)(l_Lean_Compiler_LCNF_decToMono___redArg___closed__0));
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 3, v_a_4540_);
lean_ctor_set(v___x_4533_, 1, v_a_4536_);
lean_ctor_set(v___x_4533_, 0, v___x_4544_);
v___x_4546_ = v___x_4533_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v___x_4544_);
lean_ctor_set(v_reuseFailAlloc_4551_, 1, v_a_4536_);
lean_ctor_set(v_reuseFailAlloc_4551_, 2, v_discr_4530_);
lean_ctor_set(v_reuseFailAlloc_4551_, 3, v_a_4540_);
v___x_4546_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4549_; 
v___x_4547_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4546_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v___x_4547_);
v___x_4549_ = v___x_4542_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v_a_4536_);
lean_del_object(v___x_4533_);
lean_dec(v_discr_4530_);
v_a_4553_ = lean_ctor_get(v___x_4539_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4539_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4539_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4539_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
else
{
lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4568_; 
lean_del_object(v___x_4533_);
lean_dec_ref(v_alts_4531_);
lean_dec(v_discr_4530_);
v_a_4561_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4568_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4568_ == 0)
{
v___x_4563_ = v___x_4535_;
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4535_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4568_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4566_; 
if (v_isShared_4564_ == 0)
{
v___x_4566_ = v___x_4563_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4567_; 
v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
v___x_4566_ = v_reuseFailAlloc_4567_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
return v___x_4566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___redArg___boxed(lean_object* v_c_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_){
_start:
{
lean_object* v_res_4578_; 
v_res_4578_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
lean_dec(v_a_4572_);
return v_res_4578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
lean_dec(v_a_4584_);
lean_dec_ref(v_a_4583_);
lean_dec(v_a_4582_);
lean_dec_ref(v_a_4581_);
lean_dec(v_a_4580_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_4587_, lean_object* v_i_4588_, lean_object* v_bs_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
size_t v_sz_boxed_4596_; size_t v_i_boxed_4597_; lean_object* v_res_4598_; 
v_sz_boxed_4596_ = lean_unbox_usize(v_sz_4587_);
lean_dec(v_sz_4587_);
v_i_boxed_4597_ = lean_unbox_usize(v_i_4588_);
lean_dec(v_i_4588_);
v_res_4598_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_4596_, v_i_boxed_4597_, v_bs_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___redArg___boxed(lean_object* v_c_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(v_c_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_);
lean_dec(v_a_4604_);
lean_dec_ref(v_a_4603_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24___boxed(lean_object* v_sz_4607_, lean_object* v_i_4608_, lean_object* v_bs_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
size_t v_sz_boxed_4616_; size_t v_i_boxed_4617_; lean_object* v_res_4618_; 
v_sz_boxed_4616_ = lean_unbox_usize(v_sz_4607_);
lean_dec(v_sz_4607_);
v_i_boxed_4617_ = lean_unbox_usize(v_i_4608_);
lean_dec(v_i_4608_);
v_res_4618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_decToMono_spec__24(v_sz_boxed_4616_, v_i_boxed_4617_, v_bs_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4611_);
lean_dec(v___y_4610_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
lean_object* v_res_4626_; 
v_res_4626_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_4627_, lean_object* v_uintName_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4627_, v_uintName_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
lean_dec(v_a_4633_);
lean_dec_ref(v_a_4632_);
lean_dec(v_a_4631_);
lean_dec_ref(v_a_4630_);
lean_dec(v_a_4629_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec_ref(v_a_4638_);
lean_dec(v_a_4637_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v_res_4659_; 
v_res_4659_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_);
lean_dec(v_a_4657_);
lean_dec_ref(v_a_4656_);
lean_dec(v_a_4655_);
lean_dec_ref(v_a_4654_);
lean_dec(v_a_4653_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
lean_dec(v_a_4665_);
lean_dec_ref(v_a_4664_);
lean_dec(v_a_4663_);
lean_dec_ref(v_a_4662_);
lean_dec(v_a_4661_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4668_, v_a_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_);
lean_dec(v_a_4673_);
lean_dec_ref(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
lean_dec(v_a_4669_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_4676_, lean_object* v___x_4677_, lean_object* v_sz_4678_, lean_object* v_i_4679_, lean_object* v_bs_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
uint8_t v___x_52726__boxed_4687_; size_t v_sz_boxed_4688_; size_t v_i_boxed_4689_; lean_object* v_res_4690_; 
v___x_52726__boxed_4687_ = lean_unbox(v___x_4677_);
v_sz_boxed_4688_ = lean_unbox_usize(v_sz_4678_);
lean_dec(v_sz_4678_);
v_i_boxed_4689_ = lean_unbox_usize(v_i_4679_);
lean_dec(v_i_4679_);
v_res_4690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_4676_, v___x_52726__boxed_4687_, v_sz_boxed_4688_, v_i_boxed_4689_, v_bs_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v_res_4706_; 
v_res_4706_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
return v_res_4706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
lean_dec(v_a_4712_);
lean_dec_ref(v_a_4711_);
lean_dec(v_a_4710_);
lean_dec_ref(v_a_4709_);
lean_dec(v_a_4708_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18___boxed(lean_object* v___x_4715_, lean_object* v_sz_4716_, lean_object* v_i_4717_, lean_object* v_bs_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_){
_start:
{
size_t v_sz_boxed_4725_; size_t v_i_boxed_4726_; lean_object* v_res_4727_; 
v_sz_boxed_4725_ = lean_unbox_usize(v_sz_4716_);
lean_dec(v_sz_4716_);
v_i_boxed_4726_ = lean_unbox_usize(v_i_4717_);
lean_dec(v_i_4717_);
v_res_4727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNOptionToMono_spec__18(v___x_4715_, v_sz_boxed_4725_, v_i_boxed_4726_, v_bs_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
lean_dec(v___y_4723_);
lean_dec_ref(v___y_4722_);
lean_dec(v___y_4721_);
lean_dec_ref(v___y_4720_);
lean_dec(v___y_4719_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_4728_, lean_object* v_c_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_4728_, v_c_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_info_4728_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22___boxed(lean_object* v___x_4737_, lean_object* v_sz_4738_, lean_object* v_i_4739_, lean_object* v_bs_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
size_t v_sz_boxed_4747_; size_t v_i_boxed_4748_; lean_object* v_res_4749_; 
v_sz_boxed_4747_ = lean_unbox_usize(v_sz_4738_);
lean_dec(v_sz_4738_);
v_i_boxed_4748_ = lean_unbox_usize(v_i_4739_);
lean_dec(v_i_4739_);
v_res_4749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__22(v___x_4737_, v_sz_boxed_4747_, v_i_boxed_4748_, v_bs_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___y_4741_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v_res_4757_; 
v_res_4757_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_);
lean_dec(v_a_4755_);
lean_dec_ref(v_a_4754_);
lean_dec(v_a_4753_);
lean_dec_ref(v_a_4752_);
lean_dec(v_a_4751_);
lean_dec_ref(v_c_4750_);
return v_res_4757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20___boxed(lean_object* v___x_4758_, lean_object* v_sz_4759_, lean_object* v_i_4760_, lean_object* v_bs_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
size_t v_sz_boxed_4768_; size_t v_i_boxed_4769_; lean_object* v_res_4770_; 
v_sz_boxed_4768_ = lean_unbox_usize(v_sz_4759_);
lean_dec(v_sz_4759_);
v_i_boxed_4769_ = lean_unbox_usize(v_i_4760_);
lean_dec(v_i_4760_);
v_res_4770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__20(v___x_4758_, v_sz_boxed_4768_, v_i_boxed_4769_, v_bs_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_){
_start:
{
lean_object* v_res_4778_; 
v_res_4778_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_);
lean_dec(v_a_4776_);
lean_dec_ref(v_a_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_a_4773_);
lean_dec(v_a_4772_);
return v_res_4778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4779_, lean_object* v_x_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_){
_start:
{
lean_object* v___x_4787_; 
v___x_4787_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4779_, v_a_4781_, v_a_4782_, v_a_4783_, v_a_4784_, v_a_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4788_, lean_object* v_x_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4788_, v_x_4789_, v_a_4790_, v_a_4791_, v_a_4792_, v_a_4793_, v_a_4794_);
lean_dec(v_a_4794_);
lean_dec_ref(v_a_4793_);
lean_dec(v_a_4792_);
lean_dec_ref(v_a_4791_);
lean_dec(v_a_4790_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4797_, lean_object* v_x_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_){
_start:
{
lean_object* v___x_4805_; 
v___x_4805_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4797_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_);
return v___x_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4806_, lean_object* v_x_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4806_, v_x_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_);
lean_dec(v_a_4812_);
lean_dec_ref(v_a_4811_);
lean_dec(v_a_4810_);
lean_dec_ref(v_a_4809_);
lean_dec(v_a_4808_);
lean_dec_ref(v_c_4806_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4815_, lean_object* v_x_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4815_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4824_, lean_object* v_x_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_, lean_object* v_a_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4824_, v_x_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_);
lean_dec(v_a_4830_);
lean_dec_ref(v_a_4829_);
lean_dec(v_a_4828_);
lean_dec_ref(v_a_4827_);
lean_dec(v_a_4826_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4833_, lean_object* v_x_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4833_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_);
return v___x_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4842_, lean_object* v_x_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v_res_4850_; 
v_res_4850_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4842_, v_x_4843_, v_a_4844_, v_a_4845_, v_a_4846_, v_a_4847_, v_a_4848_);
lean_dec(v_a_4848_);
lean_dec_ref(v_a_4847_);
lean_dec(v_a_4846_);
lean_dec_ref(v_a_4845_);
lean_dec(v_a_4844_);
return v_res_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4851_, lean_object* v_x_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_){
_start:
{
lean_object* v___x_4859_; 
v___x_4859_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4851_, v_a_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
return v___x_4859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4860_, lean_object* v_x_4861_, lean_object* v_a_4862_, lean_object* v_a_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v_res_4868_; 
v_res_4868_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4860_, v_x_4861_, v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_);
lean_dec(v_a_4866_);
lean_dec_ref(v_a_4865_);
lean_dec(v_a_4864_);
lean_dec_ref(v_a_4863_);
lean_dec(v_a_4862_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4869_, lean_object* v_x_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v___x_4877_; 
v___x_4877_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4869_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_);
return v___x_4877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4878_, lean_object* v_x_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4878_, v_x_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_a_4880_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4887_, lean_object* v_x_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
lean_object* v___x_4895_; 
v___x_4895_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4887_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4896_, lean_object* v_x_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
lean_object* v_res_4904_; 
v_res_4904_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4896_, v_x_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_);
lean_dec(v_a_4902_);
lean_dec_ref(v_a_4901_);
lean_dec(v_a_4900_);
lean_dec_ref(v_a_4899_);
lean_dec(v_a_4898_);
return v_res_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4905_, lean_object* v_x_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_){
_start:
{
lean_object* v___x_4913_; 
v___x_4913_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4905_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_);
return v___x_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4914_, lean_object* v_x_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4914_, v_x_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec(v_a_4916_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4923_, lean_object* v_uintName_4924_, lean_object* v_x_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_, lean_object* v_a_4928_, lean_object* v_a_4929_, lean_object* v_a_4930_){
_start:
{
lean_object* v___x_4932_; 
v___x_4932_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4923_, v_uintName_4924_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4933_, lean_object* v_uintName_4934_, lean_object* v_x_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_){
_start:
{
lean_object* v_res_4942_; 
v_res_4942_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4933_, v_uintName_4934_, v_x_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
return v_res_4942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono(lean_object* v_c_4943_, lean_object* v_x_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_){
_start:
{
lean_object* v___x_4951_; 
v___x_4951_ = l_Lean_Compiler_LCNF_casesNOptionToMono___redArg(v_c_4943_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
return v___x_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNOptionToMono___boxed(lean_object* v_c_4952_, lean_object* v_x_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l_Lean_Compiler_LCNF_casesNOptionToMono(v_c_4952_, v_x_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_, v_a_4958_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
lean_dec(v_a_4954_);
return v_res_4960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4961_, lean_object* v_x_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v___x_4969_; 
v___x_4969_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4961_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
return v___x_4969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4970_, lean_object* v_x_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4970_, v_x_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_);
lean_dec(v_a_4976_);
lean_dec_ref(v_a_4975_);
lean_dec(v_a_4974_);
lean_dec_ref(v_a_4973_);
lean_dec(v_a_4972_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4979_, lean_object* v_x_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_, lean_object* v_a_4983_, lean_object* v_a_4984_, lean_object* v_a_4985_){
_start:
{
lean_object* v___x_4987_; 
v___x_4987_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4979_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
return v___x_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4988_, lean_object* v_x_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4988_, v_x_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_);
lean_dec(v_a_4994_);
lean_dec_ref(v_a_4993_);
lean_dec(v_a_4992_);
lean_dec_ref(v_a_4991_);
lean_dec(v_a_4990_);
return v_res_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono(lean_object* v_c_4997_, lean_object* v_x_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v___x_5005_; 
v___x_5005_ = l_Lean_Compiler_LCNF_decToMono___redArg(v_c_4997_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_);
return v___x_5005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_decToMono___boxed(lean_object* v_c_5006_, lean_object* v_x_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_){
_start:
{
lean_object* v_res_5014_; 
v_res_5014_ = l_Lean_Compiler_LCNF_decToMono(v_c_5006_, v_x_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_);
lean_dec(v_a_5012_);
lean_dec_ref(v_a_5011_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
return v_res_5014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_5015_, size_t v_i_5016_, lean_object* v_bs_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v___x_5024_; 
v___x_5024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_5015_, v_i_5016_, v_bs_5017_, v___y_5018_, v___y_5020_, v___y_5021_, v___y_5022_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_5025_, lean_object* v_i_5026_, lean_object* v_bs_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
size_t v_sz_boxed_5034_; size_t v_i_boxed_5035_; lean_object* v_res_5036_; 
v_sz_boxed_5034_ = lean_unbox_usize(v_sz_5025_);
lean_dec(v_sz_5025_);
v_i_boxed_5035_ = lean_unbox_usize(v_i_5026_);
lean_dec(v_i_5026_);
v_res_5036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_5034_, v_i_boxed_5035_, v_bs_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
return v_res_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_5037_, lean_object* v_v_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
if (lean_obj_tag(v_v_5038_) == 0)
{
lean_object* v_code_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5069_; 
v_code_5045_ = lean_ctor_get(v_v_5038_, 0);
v_isSharedCheck_5069_ = !lean_is_exclusive(v_v_5038_);
if (v_isSharedCheck_5069_ == 0)
{
v___x_5047_ = v_v_5038_;
v_isShared_5048_ = v_isSharedCheck_5069_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_code_5045_);
lean_dec(v_v_5038_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5069_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5049_; 
lean_inc(v___y_5043_);
lean_inc_ref(v___y_5042_);
lean_inc(v___y_5041_);
lean_inc_ref(v___y_5040_);
lean_inc(v___y_5039_);
v___x_5049_ = lean_apply_7(v_f_5037_, v_code_5045_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, lean_box(0));
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5060_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_5052_ = v___x_5049_;
v_isShared_5053_ = v_isSharedCheck_5060_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5049_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5060_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5048_ == 0)
{
lean_ctor_set(v___x_5047_, 0, v_a_5050_);
v___x_5055_ = v___x_5047_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5059_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
lean_object* v___x_5057_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set(v___x_5052_, 0, v___x_5055_);
v___x_5057_ = v___x_5052_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5068_; 
lean_del_object(v___x_5047_);
v_a_5061_ = lean_ctor_get(v___x_5049_, 0);
v_isSharedCheck_5068_ = !lean_is_exclusive(v___x_5049_);
if (v_isSharedCheck_5068_ == 0)
{
v___x_5063_ = v___x_5049_;
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5049_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5068_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5066_; 
if (v_isShared_5064_ == 0)
{
v___x_5066_ = v___x_5063_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_a_5061_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
}
}
}
else
{
lean_object* v___x_5070_; 
lean_dec_ref(v_f_5037_);
v___x_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5070_, 0, v_v_5038_);
return v___x_5070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_5071_, lean_object* v_v_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_5071_, v_v_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
lean_dec(v___y_5075_);
lean_dec_ref(v___y_5074_);
lean_dec(v___y_5073_);
return v_res_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_5080_, lean_object* v_f_5081_, lean_object* v_v_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_5081_, v_v_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_5090_, lean_object* v_f_5091_, lean_object* v_v_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
uint8_t v_pu_boxed_5099_; lean_object* v_res_5100_; 
v_pu_boxed_5099_ = lean_unbox(v_pu_5090_);
v_res_5100_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_5099_, v_f_5091_, v_v_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
lean_dec(v___y_5093_);
return v_res_5100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_toSignature_5109_; lean_object* v_value_5110_; uint8_t v_recursive_5111_; lean_object* v_inlineAttr_x3f_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5182_; 
v_toSignature_5109_ = lean_ctor_get(v_decl_5102_, 0);
v_value_5110_ = lean_ctor_get(v_decl_5102_, 1);
v_recursive_5111_ = lean_ctor_get_uint8(v_decl_5102_, sizeof(void*)*3);
v_inlineAttr_x3f_5112_ = lean_ctor_get(v_decl_5102_, 2);
v_isSharedCheck_5182_ = !lean_is_exclusive(v_decl_5102_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5114_ = v_decl_5102_;
v_isShared_5115_ = v_isSharedCheck_5182_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_inlineAttr_x3f_5112_);
lean_inc(v_value_5110_);
lean_inc(v_toSignature_5109_);
lean_dec(v_decl_5102_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5182_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v_name_5116_; lean_object* v_type_5117_; lean_object* v_params_5118_; uint8_t v_safe_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5180_; 
v_name_5116_ = lean_ctor_get(v_toSignature_5109_, 0);
v_type_5117_ = lean_ctor_get(v_toSignature_5109_, 2);
v_params_5118_ = lean_ctor_get(v_toSignature_5109_, 3);
v_safe_5119_ = lean_ctor_get_uint8(v_toSignature_5109_, sizeof(void*)*4);
v_isSharedCheck_5180_ = !lean_is_exclusive(v_toSignature_5109_);
if (v_isSharedCheck_5180_ == 0)
{
lean_object* v_unused_5181_; 
v_unused_5181_ = lean_ctor_get(v_toSignature_5109_, 1);
lean_dec(v_unused_5181_);
v___x_5121_ = v_toSignature_5109_;
v_isShared_5122_ = v_isSharedCheck_5180_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_params_5118_);
lean_inc(v_type_5117_);
lean_inc(v_name_5116_);
lean_dec(v_toSignature_5109_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5180_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5123_; 
v___x_5123_ = l_Lean_Compiler_LCNF_toMonoType(v_type_5117_, v_a_5106_, v_a_5107_);
if (lean_obj_tag(v___x_5123_) == 0)
{
lean_object* v_a_5124_; size_t v_sz_5125_; size_t v___x_5126_; lean_object* v___x_5127_; 
v_a_5124_ = lean_ctor_get(v___x_5123_, 0);
lean_inc(v_a_5124_);
lean_dec_ref_known(v___x_5123_, 1);
v_sz_5125_ = lean_array_size(v_params_5118_);
v___x_5126_ = ((size_t)0ULL);
v___x_5127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_5125_, v___x_5126_, v_params_5118_, v_a_5103_, v_a_5105_, v_a_5106_, v_a_5107_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___f_5129_; lean_object* v___x_5130_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
lean_inc(v_a_5128_);
lean_dec_ref_known(v___x_5127_, 1);
v___f_5129_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_5130_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_5129_, v_value_5110_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_);
if (lean_obj_tag(v___x_5130_) == 0)
{
lean_object* v_a_5131_; lean_object* v___x_5132_; lean_object* v___x_5134_; 
v_a_5131_ = lean_ctor_get(v___x_5130_, 0);
lean_inc(v_a_5131_);
lean_dec_ref_known(v___x_5130_, 1);
v___x_5132_ = lean_box(0);
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 3, v_a_5128_);
lean_ctor_set(v___x_5121_, 2, v_a_5124_);
lean_ctor_set(v___x_5121_, 1, v___x_5132_);
v___x_5134_ = v___x_5121_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_name_5116_);
lean_ctor_set(v_reuseFailAlloc_5155_, 1, v___x_5132_);
lean_ctor_set(v_reuseFailAlloc_5155_, 2, v_a_5124_);
lean_ctor_set(v_reuseFailAlloc_5155_, 3, v_a_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5155_, sizeof(void*)*4, v_safe_5119_);
v___x_5134_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
lean_object* v___x_5136_; 
if (v_isShared_5115_ == 0)
{
lean_ctor_set(v___x_5114_, 1, v_a_5131_);
lean_ctor_set(v___x_5114_, 0, v___x_5134_);
v___x_5136_ = v___x_5114_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5134_);
lean_ctor_set(v_reuseFailAlloc_5154_, 1, v_a_5131_);
lean_ctor_set(v_reuseFailAlloc_5154_, 2, v_inlineAttr_x3f_5112_);
lean_ctor_set_uint8(v_reuseFailAlloc_5154_, sizeof(void*)*3, v_recursive_5111_);
v___x_5136_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
lean_object* v___x_5137_; 
lean_inc_ref(v___x_5136_);
v___x_5137_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_5136_, v_a_5107_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5144_ == 0)
{
lean_object* v_unused_5145_; 
v_unused_5145_ = lean_ctor_get(v___x_5137_, 0);
lean_dec(v_unused_5145_);
v___x_5139_ = v___x_5137_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_dec(v___x_5137_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
lean_ctor_set(v___x_5139_, 0, v___x_5136_);
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___x_5136_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_dec_ref(v___x_5136_);
v_a_5146_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5137_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5137_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
}
}
else
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5163_; 
lean_dec(v_a_5128_);
lean_dec(v_a_5124_);
lean_del_object(v___x_5121_);
lean_dec(v_name_5116_);
lean_del_object(v___x_5114_);
lean_dec(v_inlineAttr_x3f_5112_);
v_a_5156_ = lean_ctor_get(v___x_5130_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5130_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5158_ = v___x_5130_;
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5130_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5163_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5161_; 
if (v_isShared_5159_ == 0)
{
v___x_5161_ = v___x_5158_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec(v_a_5124_);
lean_del_object(v___x_5121_);
lean_dec(v_name_5116_);
lean_del_object(v___x_5114_);
lean_dec(v_inlineAttr_x3f_5112_);
lean_dec_ref(v_value_5110_);
v_a_5164_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5127_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5127_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
else
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5179_; 
lean_del_object(v___x_5121_);
lean_dec_ref(v_params_5118_);
lean_dec(v_name_5116_);
lean_del_object(v___x_5114_);
lean_dec(v_inlineAttr_x3f_5112_);
lean_dec_ref(v_value_5110_);
v_a_5172_ = lean_ctor_get(v___x_5123_, 0);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5123_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5174_ = v___x_5123_;
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5123_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5179_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5177_; 
if (v_isShared_5175_ == 0)
{
v___x_5177_ = v___x_5174_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5172_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_);
lean_dec(v_a_5188_);
lean_dec_ref(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
lean_dec(v_a_5184_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_){
_start:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5197_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_5198_ = lean_st_mk_ref(v___x_5197_);
v___x_5199_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_5191_, v___x_5198_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; lean_object* v___x_5202_; uint8_t v_isShared_5203_; uint8_t v_isSharedCheck_5208_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5199_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5202_ = v___x_5199_;
v_isShared_5203_ = v_isSharedCheck_5208_;
goto v_resetjp_5201_;
}
else
{
lean_inc(v_a_5200_);
lean_dec(v___x_5199_);
v___x_5202_ = lean_box(0);
v_isShared_5203_ = v_isSharedCheck_5208_;
goto v_resetjp_5201_;
}
v_resetjp_5201_:
{
lean_object* v___x_5204_; lean_object* v___x_5206_; 
v___x_5204_ = lean_st_ref_get(v___x_5198_);
lean_dec(v___x_5198_);
lean_dec(v___x_5204_);
if (v_isShared_5203_ == 0)
{
v___x_5206_ = v___x_5202_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v_a_5200_);
v___x_5206_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
return v___x_5206_;
}
}
}
else
{
lean_dec(v___x_5198_);
return v___x_5199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
lean_dec(v_a_5211_);
lean_dec_ref(v_a_5210_);
return v_res_5215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_5216_, size_t v_i_5217_, lean_object* v_bs_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
uint8_t v___x_5224_; 
v___x_5224_ = lean_usize_dec_lt(v_i_5217_, v_sz_5216_);
if (v___x_5224_ == 0)
{
lean_object* v___x_5225_; 
v___x_5225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5225_, 0, v_bs_5218_);
return v___x_5225_;
}
else
{
lean_object* v_v_5226_; lean_object* v___x_5227_; 
v_v_5226_ = lean_array_uget_borrowed(v_bs_5218_, v_i_5217_);
lean_inc(v_v_5226_);
v___x_5227_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_5226_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
if (lean_obj_tag(v___x_5227_) == 0)
{
lean_object* v_a_5228_; lean_object* v___x_5229_; lean_object* v_bs_x27_5230_; size_t v___x_5231_; size_t v___x_5232_; lean_object* v___x_5233_; 
v_a_5228_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5228_);
lean_dec_ref_known(v___x_5227_, 1);
v___x_5229_ = lean_unsigned_to_nat(0u);
v_bs_x27_5230_ = lean_array_uset(v_bs_5218_, v_i_5217_, v___x_5229_);
v___x_5231_ = ((size_t)1ULL);
v___x_5232_ = lean_usize_add(v_i_5217_, v___x_5231_);
v___x_5233_ = lean_array_uset(v_bs_x27_5230_, v_i_5217_, v_a_5228_);
v_i_5217_ = v___x_5232_;
v_bs_5218_ = v___x_5233_;
goto _start;
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
lean_dec_ref(v_bs_5218_);
v_a_5235_ = lean_ctor_get(v___x_5227_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5227_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5227_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5227_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_5243_, lean_object* v_i_5244_, lean_object* v_bs_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
size_t v_sz_boxed_5251_; size_t v_i_boxed_5252_; lean_object* v_res_5253_; 
v_sz_boxed_5251_ = lean_unbox_usize(v_sz_5243_);
lean_dec(v_sz_5243_);
v_i_boxed_5252_ = lean_unbox_usize(v_i_5244_);
lean_dec(v_i_5244_);
v_res_5253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_5251_, v_i_boxed_5252_, v_bs_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v___y_5247_);
lean_dec_ref(v___y_5246_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
size_t v_sz_5260_; size_t v___x_5261_; lean_object* v___x_5262_; 
v_sz_5260_ = lean_array_size(v_x_5254_);
v___x_5261_ = ((size_t)0ULL);
v___x_5262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_5260_, v___x_5261_, v_x_5254_, v___y_5255_, v___y_5256_, v___y_5257_, v___y_5258_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5352_; uint8_t v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5352_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_5353_ = 1;
v___x_5354_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_5355_ = l_Lean_registerTraceClass(v___x_5352_, v___x_5353_, v___x_5354_);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_5357_;
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
