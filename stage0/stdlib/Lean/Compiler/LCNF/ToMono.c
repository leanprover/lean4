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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toMonoType(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isTypeFormerType(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedLetValue_default___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "expected inductive type"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Compiler.LCNF.Code.toMono"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Compiler.LCNF.Basic"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_Code_toMono___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__5;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5_value;
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
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Thunk"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
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
static lean_once_cell_t l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 106, 49, 240, 167, 66, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(lean_object*, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 110, 84, 99, 226, 14, 63, 127)}};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_188_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_189_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
v___x_190_ = lean_st_ref_get(v_a_185_);
lean_inc(v_fvarId_187_);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_188_, v___x_189_, v___x_190_, v_fvarId_187_);
lean_dec(v___x_190_);
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
v___x_216_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_217_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
v___x_218_ = lean_st_ref_get(v_a_209_);
lean_inc(v_fvarId_215_);
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_216_, v___x_217_, v___x_218_, v_fvarId_215_);
lean_dec(v___x_218_);
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
v___x_532_ = l_instMonadEIO___redArg();
return v___x_532_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default___redArg();
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_toApplicative_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_609_; 
v___x_545_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_546_ = l_StateRefT_x27_instMonad___redArg(v___x_545_);
v_toApplicative_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v___x_546_, 1);
lean_dec(v_unused_610_);
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_609_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_toApplicative_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_609_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v_toFunctor_551_; lean_object* v_toSeq_552_; lean_object* v_toSeqLeft_553_; lean_object* v_toSeqRight_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_607_; 
v_toFunctor_551_ = lean_ctor_get(v_toApplicative_547_, 0);
v_toSeq_552_ = lean_ctor_get(v_toApplicative_547_, 2);
v_toSeqLeft_553_ = lean_ctor_get(v_toApplicative_547_, 3);
v_toSeqRight_554_ = lean_ctor_get(v_toApplicative_547_, 4);
v_isSharedCheck_607_ = !lean_is_exclusive(v_toApplicative_547_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v_toApplicative_547_, 1);
lean_dec(v_unused_608_);
v___x_556_ = v_toApplicative_547_;
v_isShared_557_ = v_isSharedCheck_607_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_toSeqRight_554_);
lean_inc(v_toSeqLeft_553_);
lean_inc(v_toSeq_552_);
lean_inc(v_toFunctor_551_);
lean_dec(v_toApplicative_547_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_607_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___f_558_; lean_object* v___f_559_; lean_object* v___f_560_; lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___f_563_; lean_object* v___f_564_; lean_object* v___f_565_; lean_object* v___x_567_; 
v___f_558_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_559_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_551_);
v___f_560_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_560_, 0, v_toFunctor_551_);
v___f_561_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_561_, 0, v_toFunctor_551_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___f_560_);
lean_ctor_set(v___x_562_, 1, v___f_561_);
v___f_563_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_563_, 0, v_toSeqRight_554_);
v___f_564_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_564_, 0, v_toSeqLeft_553_);
v___f_565_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_565_, 0, v_toSeq_552_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 4, v___f_563_);
lean_ctor_set(v___x_556_, 3, v___f_564_);
lean_ctor_set(v___x_556_, 2, v___f_565_);
lean_ctor_set(v___x_556_, 1, v___f_558_);
lean_ctor_set(v___x_556_, 0, v___x_562_);
v___x_567_ = v___x_556_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___f_558_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v___f_565_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v___f_564_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v___f_563_);
v___x_567_ = v_reuseFailAlloc_606_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___f_559_);
lean_ctor_set(v___x_549_, 0, v___x_567_);
v___x_569_ = v___x_549_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___f_559_);
v___x_569_ = v_reuseFailAlloc_605_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v_toApplicative_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_603_; 
v___x_570_ = l_StateRefT_x27_instMonad___redArg(v___x_569_);
v_toApplicative_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_603_ == 0)
{
lean_object* v_unused_604_; 
v_unused_604_ = lean_ctor_get(v___x_570_, 1);
lean_dec(v_unused_604_);
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_603_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_toApplicative_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_603_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_toFunctor_575_; lean_object* v_toSeq_576_; lean_object* v_toSeqLeft_577_; lean_object* v_toSeqRight_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_toFunctor_575_ = lean_ctor_get(v_toApplicative_571_, 0);
v_toSeq_576_ = lean_ctor_get(v_toApplicative_571_, 2);
v_toSeqLeft_577_ = lean_ctor_get(v_toApplicative_571_, 3);
v_toSeqRight_578_ = lean_ctor_get(v_toApplicative_571_, 4);
v_isSharedCheck_601_ = !lean_is_exclusive(v_toApplicative_571_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_toApplicative_571_, 1);
lean_dec(v_unused_602_);
v___x_580_ = v_toApplicative_571_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_toSeqRight_578_);
lean_inc(v_toSeqLeft_577_);
lean_inc(v_toSeq_576_);
lean_inc(v_toFunctor_575_);
lean_dec(v_toApplicative_571_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___x_591_; 
v___f_582_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_583_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_575_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_584_, 0, v_toFunctor_575_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_585_, 0, v_toFunctor_575_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___f_584_);
lean_ctor_set(v___x_586_, 1, v___f_585_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_587_, 0, v_toSeqRight_578_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_588_, 0, v_toSeqLeft_577_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_589_, 0, v_toSeq_576_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 4, v___f_587_);
lean_ctor_set(v___x_580_, 3, v___f_588_);
lean_ctor_set(v___x_580_, 2, v___f_589_);
lean_ctor_set(v___x_580_, 1, v___f_582_);
lean_ctor_set(v___x_580_, 0, v___x_586_);
v___x_591_ = v___x_580_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___f_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v___f_589_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v___f_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v___f_587_);
v___x_591_ = v_reuseFailAlloc_600_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v___f_583_);
lean_ctor_set(v___x_573_, 0, v___x_591_);
v___x_593_ = v___x_573_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___f_583_);
v___x_593_ = v_reuseFailAlloc_599_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_6341__overap_597_; lean_object* v___x_598_; 
v___x_594_ = l_StateRefT_x27_instMonad___redArg(v___x_593_);
v___x_595_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_596_ = l_instInhabitedOfMonad___redArg(v___x_594_, v___x_595_);
v___x_6341__overap_597_ = lean_panic_fn_borrowed(v___x_596_, v_msg_538_);
lean_dec(v___x_596_);
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
lean_inc(v___y_539_);
v___x_598_ = lean_apply_6(v___x_6341__overap_597_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, lean_box(0));
return v___x_598_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object* v_upperBound_619_, lean_object* v_args_620_, lean_object* v_a_621_, lean_object* v_b_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_a_626_; uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_lt(v_a_621_, v_upperBound_619_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; 
lean_dec(v_a_621_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v_b_622_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(0);
v___x_634_ = lean_array_get_borrowed(v___x_633_, v_args_620_, v_a_621_);
if (lean_obj_tag(v___x_634_) == 1)
{
lean_object* v_fvarId_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_fvarId_635_ = lean_ctor_get(v___x_634_, 0);
v___x_636_ = lean_st_ref_get(v___y_623_);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_636_, v_fvarId_635_);
lean_dec(v___x_636_);
if (v___x_637_ == 0)
{
lean_inc_ref(v___x_634_);
v_a_626_ = v___x_634_;
goto v___jp_625_;
}
else
{
v_a_626_ = v___x_633_;
goto v___jp_625_;
}
}
else
{
v_a_626_ = v___x_633_;
goto v___jp_625_;
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_array_push(v_b_622_, v_a_626_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_a_621_, v___x_628_);
lean_dec(v_a_621_);
v_a_621_ = v___x_629_;
v_b_622_ = v___x_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object* v_upperBound_638_, lean_object* v_args_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_638_, v_args_639_, v_a_640_, v_b_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v_args_639_);
lean_dec(v_upperBound_638_);
return v_res_644_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__13(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_666_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_667_ = lean_unsigned_to_nat(6u);
v___x_668_ = lean_unsigned_to_nat(83u);
v___x_669_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_670_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_671_ = l_mkPanicMessageWithDecl(v___x_670_, v___x_669_, v___x_668_, v___x_667_, v___x_666_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
switch(lean_obj_tag(v_e_676_))
{
case 2:
{
lean_object* v_typeName_683_; lean_object* v_idx_684_; lean_object* v_struct_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_typeName_683_ = lean_ctor_get(v_e_676_, 0);
v_idx_684_ = lean_ctor_get(v_e_676_, 1);
v_struct_685_ = lean_ctor_get(v_e_676_, 2);
v___x_686_ = lean_st_ref_get(v_a_677_);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_686_, v_struct_685_);
lean_dec(v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_inc(v_typeName_683_);
v___x_688_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_683_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_708_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_708_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
if (lean_obj_tag(v_a_689_) == 1)
{
lean_object* v_val_693_; lean_object* v_fieldIdx_694_; uint8_t v___x_695_; 
lean_inc(v_struct_685_);
lean_inc(v_idx_684_);
lean_dec_ref_known(v_e_676_, 3);
v_val_693_ = lean_ctor_get(v_a_689_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v_a_689_, 1);
v_fieldIdx_694_ = lean_ctor_get(v_val_693_, 2);
lean_inc(v_fieldIdx_694_);
lean_dec(v_val_693_);
v___x_695_ = lean_nat_dec_eq(v_fieldIdx_694_, v_idx_684_);
lean_dec(v_idx_684_);
lean_dec(v_fieldIdx_694_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec(v_struct_685_);
v___x_696_ = lean_box(1);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_696_);
v___x_698_ = v___x_691_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_701_, 0, v_struct_685_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_701_);
v___x_703_ = v___x_691_;
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
}
else
{
lean_object* v___x_706_; 
lean_dec(v_a_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v_e_676_);
v___x_706_ = v___x_691_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_e_676_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref_known(v_e_676_, 3);
v_a_709_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_688_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_688_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec_ref_known(v_e_676_, 3);
v___x_717_ = lean_box(1);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
case 3:
{
lean_object* v_declName_719_; lean_object* v_args_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_842_; 
v_declName_719_ = lean_ctor_get(v_e_676_, 0);
v_args_720_ = lean_ctor_get(v_e_676_, 2);
v_isSharedCheck_842_ = !lean_is_exclusive(v_e_676_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_e_676_, 1);
lean_dec(v_unused_843_);
v___x_722_ = v_e_676_;
v_isShared_723_ = v_isSharedCheck_842_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_args_720_);
lean_inc(v_declName_719_);
lean_dec(v_e_676_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_842_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_args_725_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__2));
v___x_773_ = lean_name_eq(v_declName_719_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_775_ = lean_name_eq(v_declName_719_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__7));
v___x_777_ = lean_name_eq(v_declName_719_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_779_ = lean_name_eq(v_declName_719_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v_env_781_; lean_object* v___x_782_; 
v___x_780_ = lean_st_ref_get(v_a_681_);
v_env_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_ref(v_env_781_);
lean_dec(v___x_780_);
lean_inc(v_declName_719_);
v___x_782_ = l_Lean_Environment_find_x3f(v_env_781_, v_declName_719_, v___x_779_);
if (lean_obj_tag(v___x_782_) == 1)
{
lean_object* v_val_783_; 
v_val_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_783_);
lean_dec_ref_known(v___x_782_, 1);
if (lean_obj_tag(v_val_783_) == 6)
{
lean_object* v_val_784_; lean_object* v_induct_785_; lean_object* v_numParams_786_; lean_object* v___x_787_; 
lean_del_object(v___x_722_);
lean_dec(v_declName_719_);
v_val_784_ = lean_ctor_get(v_val_783_, 0);
lean_inc_ref(v_val_784_);
lean_dec_ref_known(v_val_783_, 1);
v_induct_785_ = lean_ctor_get(v_val_784_, 1);
v_numParams_786_ = lean_ctor_get(v_val_784_, 3);
lean_inc(v_induct_785_);
v___x_787_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_785_, v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_787_, 1);
if (lean_obj_tag(v_a_788_) == 1)
{
lean_object* v_val_789_; lean_object* v_fieldIdx_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc(v_numParams_786_);
lean_dec_ref(v_val_784_);
v_val_789_ = lean_ctor_get(v_a_788_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_a_788_, 1);
v_fieldIdx_790_ = lean_ctor_get(v_val_789_, 2);
lean_inc(v_fieldIdx_790_);
lean_dec(v_val_789_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_nat_add(v_numParams_786_, v_fieldIdx_790_);
lean_dec(v_fieldIdx_790_);
lean_dec(v_numParams_786_);
v___x_793_ = lean_array_get(v___x_791_, v_args_720_, v___x_792_);
lean_dec(v___x_792_);
lean_dec_ref(v_args_720_);
v___x_794_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_793_);
lean_dec(v___x_793_);
v_e_676_ = v___x_794_;
goto _start;
}
else
{
lean_object* v___x_796_; 
lean_dec(v_a_788_);
v___x_796_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_784_, v_args_720_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
return v___x_796_;
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_val_784_);
lean_dec_ref(v_args_720_);
v_a_797_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_787_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_787_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_dec(v_val_783_);
v___y_732_ = v_a_677_;
v___y_733_ = v_a_678_;
v___y_734_ = v_a_679_;
v___y_735_ = v_a_680_;
v___y_736_ = v_a_681_;
goto v___jp_731_;
}
}
else
{
lean_dec(v___x_782_);
v___y_732_ = v_a_677_;
v___y_733_ = v_a_678_;
v___y_734_ = v_a_679_;
v___y_735_ = v_a_680_;
v___y_736_ = v_a_681_;
goto v___jp_731_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_declName_719_);
v___x_805_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__13, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__13);
v___x_806_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_805_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
return v___x_806_;
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_declName_719_);
v___x_807_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_del_object(v___x_722_);
lean_dec(v_declName_719_);
v___x_809_ = lean_box(0);
v___x_810_ = lean_unsigned_to_nat(2u);
v___x_811_ = lean_array_get_borrowed(v___x_809_, v_args_720_, v___x_810_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_fvarId_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v_extraArgs_816_; lean_object* v___x_817_; 
v_fvarId_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_fvarId_812_);
v___x_813_ = lean_array_get_size(v_args_720_);
v___x_814_ = lean_unsigned_to_nat(3u);
v___x_815_ = lean_nat_sub(v___x_813_, v___x_814_);
v_extraArgs_816_ = lean_mk_empty_array_with_capacity(v___x_815_);
lean_dec(v___x_815_);
v___x_817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_813_, v_args_720_, v___x_814_, v_extraArgs_816_, v_a_677_);
lean_dec_ref(v_args_720_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_822_, 0, v_fvarId_812_);
lean_ctor_set(v___x_822_, 1, v_a_818_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
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
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_fvarId_812_);
v_a_827_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_817_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_817_);
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
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v_args_720_);
v___x_835_ = lean_box(1);
v___x_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
return v___x_836_;
}
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_722_);
lean_dec(v_declName_719_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_unsigned_to_nat(2u);
v___x_839_ = lean_array_get(v___x_837_, v_args_720_, v___x_838_);
lean_dec_ref(v_args_720_);
v___x_840_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_839_);
lean_dec(v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
return v___x_841_;
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_box(0);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 2, v_args_725_);
lean_ctor_set(v___x_722_, 1, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_declName_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_args_725_);
v___x_728_ = v_reuseFailAlloc_730_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
v___jp_731_:
{
lean_object* v___x_737_; 
lean_inc(v_declName_719_);
v___x_737_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_719_, v___y_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
if (lean_obj_tag(v_a_738_) == 1)
{
lean_object* v_val_739_; lean_object* v_toSignature_740_; lean_object* v_type_741_; lean_object* v___x_742_; 
v_val_739_ = lean_ctor_get(v_a_738_, 0);
lean_inc(v_val_739_);
lean_dec_ref_known(v_a_738_, 1);
v_toSignature_740_ = lean_ctor_get(v_val_739_, 0);
lean_inc_ref(v_toSignature_740_);
lean_dec(v_val_739_);
v_type_741_ = lean_ctor_get(v_toSignature_740_, 2);
lean_inc_ref(v_type_741_);
lean_dec_ref(v_toSignature_740_);
v___x_742_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_720_, v_type_741_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec_ref(v_args_720_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v_args_725_ = v_a_743_;
goto v___jp_724_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_del_object(v___x_722_);
lean_dec(v_declName_719_);
v_a_744_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_742_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
size_t v_sz_752_; size_t v___x_753_; lean_object* v___x_754_; 
lean_dec(v_a_738_);
v_sz_752_ = lean_array_size(v_args_720_);
v___x_753_ = ((size_t)0ULL);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_752_, v___x_753_, v_args_720_, v___y_732_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v_args_725_ = v_a_755_;
goto v___jp_724_;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_del_object(v___x_722_);
lean_dec(v_declName_719_);
v_a_756_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_754_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_754_);
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
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_args_720_);
lean_dec(v_declName_719_);
v_a_764_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_737_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_737_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_844_; lean_object* v_args_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_875_; 
v_fvarId_844_ = lean_ctor_get(v_e_676_, 0);
v_args_845_ = lean_ctor_get(v_e_676_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v_e_676_);
if (v_isSharedCheck_875_ == 0)
{
v___x_847_ = v_e_676_;
v_isShared_848_ = v_isSharedCheck_875_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_args_845_);
lean_inc(v_fvarId_844_);
lean_dec(v_e_676_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_875_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_st_ref_get(v_a_677_);
v___x_850_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_849_, v_fvarId_844_);
lean_dec(v___x_849_);
if (v___x_850_ == 0)
{
size_t v_sz_851_; size_t v___x_852_; lean_object* v___x_853_; 
v_sz_851_ = lean_array_size(v_args_845_);
v___x_852_ = ((size_t)0ULL);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_851_, v___x_852_, v_args_845_, v_a_677_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_864_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_864_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_864_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_a_854_);
v___x_859_ = v___x_847_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fvarId_844_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_a_854_);
v___x_859_ = v_reuseFailAlloc_863_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_859_);
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_del_object(v___x_847_);
lean_dec(v_fvarId_844_);
v_a_865_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_853_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_853_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; 
lean_del_object(v___x_847_);
lean_dec_ref(v_args_845_);
lean_dec(v_fvarId_844_);
v___x_873_ = lean_box(1);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
}
}
default: 
{
lean_object* v___x_876_; 
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_e_676_);
return v___x_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_885_, lean_object* v_args_886_, lean_object* v_inst_887_, lean_object* v_R_888_, lean_object* v_a_889_, lean_object* v_b_890_, lean_object* v_c_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_885_, v_args_886_, v_a_889_, v_b_890_, v___y_892_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_899_, lean_object* v_args_900_, lean_object* v_inst_901_, lean_object* v_R_902_, lean_object* v_a_903_, lean_object* v_b_904_, lean_object* v_c_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_899_, v_args_900_, v_inst_901_, v_R_902_, v_a_903_, v_b_904_, v_c_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v_args_900_);
lean_dec(v_upperBound_899_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_type_920_; lean_object* v_value_921_; lean_object* v___x_922_; 
v_type_920_ = lean_ctor_get(v_decl_913_, 2);
v_value_921_ = lean_ctor_get(v_decl_913_, 3);
lean_inc_ref(v_type_920_);
v___x_922_ = l_Lean_Compiler_LCNF_toMonoType(v_type_920_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_924_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
lean_inc(v_value_921_);
v___x_924_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_921_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v___x_926_ = 0;
v___x_927_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_926_, v_decl_913_, v_a_923_, v_a_925_, v_a_916_);
return v___x_927_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_a_923_);
lean_dec_ref(v_decl_913_);
v_a_928_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_924_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v_decl_913_);
v_a_936_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_922_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_922_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
lean_dec(v_a_945_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_toApplicative_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1023_; 
v___x_959_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_960_ = l_StateRefT_x27_instMonad___redArg(v___x_959_);
v_toApplicative_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v___x_960_, 1);
lean_dec(v_unused_1024_);
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_1023_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_toApplicative_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1023_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v_toFunctor_965_; lean_object* v_toSeq_966_; lean_object* v_toSeqLeft_967_; lean_object* v_toSeqRight_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_1021_; 
v_toFunctor_965_ = lean_ctor_get(v_toApplicative_961_, 0);
v_toSeq_966_ = lean_ctor_get(v_toApplicative_961_, 2);
v_toSeqLeft_967_ = lean_ctor_get(v_toApplicative_961_, 3);
v_toSeqRight_968_ = lean_ctor_get(v_toApplicative_961_, 4);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_toApplicative_961_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v_toApplicative_961_, 1);
lean_dec(v_unused_1022_);
v___x_970_ = v_toApplicative_961_;
v_isShared_971_ = v_isSharedCheck_1021_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_toSeqRight_968_);
lean_inc(v_toSeqLeft_967_);
lean_inc(v_toSeq_966_);
lean_inc(v_toFunctor_965_);
lean_dec(v_toApplicative_961_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_1021_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___f_972_; lean_object* v___f_973_; lean_object* v___f_974_; lean_object* v___f_975_; lean_object* v___x_976_; lean_object* v___f_977_; lean_object* v___f_978_; lean_object* v___f_979_; lean_object* v___x_981_; 
v___f_972_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_973_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_965_);
v___f_974_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_974_, 0, v_toFunctor_965_);
v___f_975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_975_, 0, v_toFunctor_965_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___f_974_);
lean_ctor_set(v___x_976_, 1, v___f_975_);
v___f_977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_977_, 0, v_toSeqRight_968_);
v___f_978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_978_, 0, v_toSeqLeft_967_);
v___f_979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_979_, 0, v_toSeq_966_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 4, v___f_977_);
lean_ctor_set(v___x_970_, 3, v___f_978_);
lean_ctor_set(v___x_970_, 2, v___f_979_);
lean_ctor_set(v___x_970_, 1, v___f_972_);
lean_ctor_set(v___x_970_, 0, v___x_976_);
v___x_981_ = v___x_970_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v___f_972_);
lean_ctor_set(v_reuseFailAlloc_1020_, 2, v___f_979_);
lean_ctor_set(v_reuseFailAlloc_1020_, 3, v___f_978_);
lean_ctor_set(v_reuseFailAlloc_1020_, 4, v___f_977_);
v___x_981_ = v_reuseFailAlloc_1020_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___f_973_);
lean_ctor_set(v___x_963_, 0, v___x_981_);
v___x_983_ = v___x_963_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___f_973_);
v___x_983_ = v_reuseFailAlloc_1019_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; lean_object* v_toApplicative_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1017_; 
v___x_984_ = l_StateRefT_x27_instMonad___redArg(v___x_983_);
v_toApplicative_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_984_, 1);
lean_dec(v_unused_1018_);
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_1017_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_toApplicative_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1017_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_toFunctor_989_; lean_object* v_toSeq_990_; lean_object* v_toSeqLeft_991_; lean_object* v_toSeqRight_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1015_; 
v_toFunctor_989_ = lean_ctor_get(v_toApplicative_985_, 0);
v_toSeq_990_ = lean_ctor_get(v_toApplicative_985_, 2);
v_toSeqLeft_991_ = lean_ctor_get(v_toApplicative_985_, 3);
v_toSeqRight_992_ = lean_ctor_get(v_toApplicative_985_, 4);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_toApplicative_985_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; 
v_unused_1016_ = lean_ctor_get(v_toApplicative_985_, 1);
lean_dec(v_unused_1016_);
v___x_994_ = v_toApplicative_985_;
v_isShared_995_ = v_isSharedCheck_1015_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_toSeqRight_992_);
lean_inc(v_toSeqLeft_991_);
lean_inc(v_toSeq_990_);
lean_inc(v_toFunctor_989_);
lean_dec(v_toApplicative_985_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1015_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___x_1005_; 
v___f_996_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_997_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_989_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_998_, 0, v_toFunctor_989_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_999_, 0, v_toFunctor_989_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___f_998_);
lean_ctor_set(v___x_1000_, 1, v___f_999_);
v___f_1001_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1001_, 0, v_toSeqRight_992_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toSeqLeft_991_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toSeq_990_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 4, v___f_1001_);
lean_ctor_set(v___x_994_, 3, v___f_1002_);
lean_ctor_set(v___x_994_, 2, v___f_1003_);
lean_ctor_set(v___x_994_, 1, v___f_996_);
lean_ctor_set(v___x_994_, 0, v___x_1000_);
v___x_1005_ = v___x_994_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v___f_996_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v___f_1003_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v___f_1002_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v___f_1001_);
v___x_1005_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___f_997_);
lean_ctor_set(v___x_987_, 0, v___x_1005_);
v___x_1007_ = v___x_987_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___f_997_);
v___x_1007_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_4525__overap_1011_; lean_object* v___x_1012_; 
v___x_1008_ = l_StateRefT_x27_instMonad___redArg(v___x_1007_);
v___x_1009_ = lean_box(0);
v___x_1010_ = l_instInhabitedOfMonad___redArg(v___x_1008_, v___x_1009_);
v___x_4525__overap_1011_ = lean_panic_fn_borrowed(v___x_1010_, v_msg_952_);
lean_dec(v___x_1010_);
lean_inc(v___y_957_);
lean_inc_ref(v___y_956_);
lean_inc(v___y_955_);
lean_inc_ref(v___y_954_);
lean_inc(v___y_953_);
v___x_1012_ = lean_apply_6(v___x_4525__overap_1011_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, lean_box(0));
return v___x_1012_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
return v_res_1032_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1034_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1035_ = lean_unsigned_to_nat(11u);
v___x_1036_ = lean_unsigned_to_nat(124u);
v___x_1037_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1038_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1039_ = l_mkPanicMessageWithDecl(v___x_1038_, v___x_1037_, v___x_1036_, v___x_1035_, v___x_1034_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1040_, lean_object* v_a_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_a_1050_; uint8_t v___x_1054_; 
v___x_1054_ = lean_nat_dec_lt(v_a_1041_, v_upperBound_1040_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec(v_a_1041_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_b_1042_);
return v___x_1055_;
}
else
{
if (lean_obj_tag(v_b_1042_) == 7)
{
lean_object* v_body_1056_; 
v_body_1056_ = lean_ctor_get(v_b_1042_, 2);
lean_inc_ref(v_body_1056_);
lean_dec_ref_known(v_b_1042_, 3);
v_a_1050_ = v_body_1056_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1058_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1057_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_dec_ref_known(v___x_1058_, 1);
v_a_1050_ = v_b_1042_;
goto v___jp_1049_;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_b_1042_);
lean_dec(v_a_1041_);
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
v___jp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = lean_nat_add(v_a_1041_, v___x_1051_);
lean_dec(v_a_1041_);
v_a_1041_ = v___x_1052_;
v_b_1042_ = v_a_1050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1067_, lean_object* v_a_1068_, lean_object* v_b_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1067_, v_a_1068_, v_b_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v_upperBound_1067_);
return v_res_1076_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1077_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1078_ = lean_unsigned_to_nat(11u);
v___x_1079_ = lean_unsigned_to_nat(132u);
v___x_1080_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1081_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1082_ = l_mkPanicMessageWithDecl(v___x_1081_, v___x_1080_, v___x_1079_, v___x_1078_, v___x_1077_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_a_1093_; uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_lt(v_a_1084_, v_upperBound_1083_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v_a_1084_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_b_1085_);
return v___x_1098_;
}
else
{
lean_object* v_fst_1099_; 
v_fst_1099_ = lean_ctor_get(v_b_1085_, 0);
lean_inc(v_fst_1099_);
if (lean_obj_tag(v_fst_1099_) == 7)
{
lean_object* v_snd_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1133_; 
v_snd_1100_ = lean_ctor_get(v_b_1085_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_b_1085_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_b_1085_, 0);
lean_dec(v_unused_1134_);
v___x_1102_ = v_b_1085_;
v_isShared_1103_ = v_isSharedCheck_1133_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snd_1100_);
lean_dec(v_b_1085_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1133_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_binderName_1104_; lean_object* v_binderType_1105_; lean_object* v_body_1106_; lean_object* v___x_1107_; 
v_binderName_1104_ = lean_ctor_get(v_fst_1099_, 0);
lean_inc(v_binderName_1104_);
v_binderType_1105_ = lean_ctor_get(v_fst_1099_, 1);
lean_inc_ref(v_binderType_1105_);
v_body_1106_ = lean_ctor_get(v_fst_1099_, 2);
lean_inc_ref(v_body_1106_);
lean_dec_ref_known(v_fst_1099_, 3);
v___x_1107_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1105_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; uint8_t v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = 0;
v___x_1110_ = 0;
v___x_1111_ = l_Lean_Compiler_LCNF_mkParam(v___x_1109_, v_binderName_1104_, v_a_1108_, v___x_1110_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = lean_array_push(v_snd_1100_, v_a_1112_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1113_);
lean_ctor_set(v___x_1102_, 0, v_body_1106_);
v___x_1115_ = v___x_1102_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_body_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
v_a_1093_ = v___x_1115_;
goto v___jp_1092_;
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_body_1106_);
lean_del_object(v___x_1102_);
lean_dec(v_snd_1100_);
lean_dec(v_a_1084_);
v_a_1117_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1111_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1111_);
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
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v_body_1106_);
lean_dec(v_binderName_1104_);
lean_del_object(v___x_1102_);
lean_dec(v_snd_1100_);
lean_dec(v_a_1084_);
v_a_1125_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1107_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1107_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
else
{
lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1152_; 
v_snd_1135_ = lean_ctor_get(v_b_1085_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_b_1085_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; 
v_unused_1153_ = lean_ctor_get(v_b_1085_, 0);
lean_dec(v_unused_1153_);
v___x_1137_ = v_b_1085_;
v_isShared_1138_ = v_isSharedCheck_1152_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_dec(v_b_1085_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1152_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1140_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1139_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref_known(v___x_1140_, 1);
if (v_isShared_1138_ == 0)
{
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_snd_1135_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
v_a_1093_ = v___x_1142_;
goto v___jp_1092_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_del_object(v___x_1137_);
lean_dec(v_snd_1135_);
lean_dec(v_fst_1099_);
lean_dec(v_a_1084_);
v_a_1144_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1140_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1140_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
v___jp_1092_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_add(v_a_1084_, v___x_1094_);
lean_dec(v_a_1084_);
v_a_1084_ = v___x_1095_;
v_b_1085_ = v_a_1093_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1154_, lean_object* v_a_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1154_, v_a_1155_, v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec(v_upperBound_1154_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1164_, lean_object* v_numParams_1165_, lean_object* v_numNewFields_1166_, lean_object* v_oldFields_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1165_, v___x_1174_, v_ctorType_1164_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = lean_array_get_size(v_oldFields_1167_);
v___x_1178_ = lean_nat_add(v___x_1177_, v_numNewFields_1166_);
v___x_1179_ = lean_mk_empty_array_with_capacity(v___x_1178_);
lean_dec(v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v_a_1176_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1166_, v___x_1174_, v___x_1180_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1191_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1191_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v_snd_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v_snd_1186_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_snd_1186_);
lean_dec(v_a_1182_);
v___x_1187_ = l_Array_append___redArg(v_snd_1186_, v_oldFields_1167_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1181_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1181_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1175_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1175_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1208_, lean_object* v_numParams_1209_, lean_object* v_numNewFields_1210_, lean_object* v_oldFields_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1208_, v_numParams_1209_, v_numNewFields_1210_, v_oldFields_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_oldFields_1211_);
lean_dec(v_numNewFields_1210_);
lean_dec(v_numParams_1209_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1219_, lean_object* v_inst_1220_, lean_object* v_R_1221_, lean_object* v_a_1222_, lean_object* v_b_1223_, lean_object* v_c_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1219_, v_a_1222_, v_b_1223_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1232_, lean_object* v_inst_1233_, lean_object* v_R_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_c_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1232_, v_inst_1233_, v_R_1234_, v_a_1235_, v_b_1236_, v_c_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec(v_upperBound_1232_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1245_, lean_object* v_inst_1246_, lean_object* v_R_1247_, lean_object* v_a_1248_, lean_object* v_b_1249_, lean_object* v_c_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1245_, v_a_1248_, v_b_1249_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1258_, lean_object* v_inst_1259_, lean_object* v_R_1260_, lean_object* v_a_1261_, lean_object* v_b_1262_, lean_object* v_c_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1258_, v_inst_1259_, v_R_1260_, v_a_1261_, v_b_1262_, v_c_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec(v_upperBound_1258_);
return v_res_1270_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v_toApplicative_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1343_; 
v___x_1279_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1280_ = l_StateRefT_x27_instMonad___redArg(v___x_1279_);
v_toApplicative_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; 
v_unused_1344_ = lean_ctor_get(v___x_1280_, 1);
lean_dec(v_unused_1344_);
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1343_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_toApplicative_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1343_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_toFunctor_1285_; lean_object* v_toSeq_1286_; lean_object* v_toSeqLeft_1287_; lean_object* v_toSeqRight_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1341_; 
v_toFunctor_1285_ = lean_ctor_get(v_toApplicative_1281_, 0);
v_toSeq_1286_ = lean_ctor_get(v_toApplicative_1281_, 2);
v_toSeqLeft_1287_ = lean_ctor_get(v_toApplicative_1281_, 3);
v_toSeqRight_1288_ = lean_ctor_get(v_toApplicative_1281_, 4);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_toApplicative_1281_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_toApplicative_1281_, 1);
lean_dec(v_unused_1342_);
v___x_1290_ = v_toApplicative_1281_;
v_isShared_1291_ = v_isSharedCheck_1341_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_toSeqRight_1288_);
lean_inc(v_toSeqLeft_1287_);
lean_inc(v_toSeq_1286_);
lean_inc(v_toFunctor_1285_);
lean_dec(v_toApplicative_1281_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1341_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1301_; 
v___f_1292_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1293_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1285_);
v___f_1294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1294_, 0, v_toFunctor_1285_);
v___f_1295_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1295_, 0, v_toFunctor_1285_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___f_1294_);
lean_ctor_set(v___x_1296_, 1, v___f_1295_);
v___f_1297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1297_, 0, v_toSeqRight_1288_);
v___f_1298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1298_, 0, v_toSeqLeft_1287_);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toSeq_1286_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 4, v___f_1297_);
lean_ctor_set(v___x_1290_, 3, v___f_1298_);
lean_ctor_set(v___x_1290_, 2, v___f_1299_);
lean_ctor_set(v___x_1290_, 1, v___f_1292_);
lean_ctor_set(v___x_1290_, 0, v___x_1296_);
v___x_1301_ = v___x_1290_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___f_1292_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v___f_1299_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v___f_1298_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v___f_1297_);
v___x_1301_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 1, v___f_1293_);
lean_ctor_set(v___x_1283_, 0, v___x_1301_);
v___x_1303_ = v___x_1283_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v___f_1293_);
v___x_1303_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1304_; lean_object* v_toApplicative_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1337_; 
v___x_1304_ = l_StateRefT_x27_instMonad___redArg(v___x_1303_);
v_toApplicative_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v___x_1304_, 1);
lean_dec(v_unused_1338_);
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1337_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_toApplicative_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1337_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_toFunctor_1309_; lean_object* v_toSeq_1310_; lean_object* v_toSeqLeft_1311_; lean_object* v_toSeqRight_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1335_; 
v_toFunctor_1309_ = lean_ctor_get(v_toApplicative_1305_, 0);
v_toSeq_1310_ = lean_ctor_get(v_toApplicative_1305_, 2);
v_toSeqLeft_1311_ = lean_ctor_get(v_toApplicative_1305_, 3);
v_toSeqRight_1312_ = lean_ctor_get(v_toApplicative_1305_, 4);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_toApplicative_1305_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_toApplicative_1305_, 1);
lean_dec(v_unused_1336_);
v___x_1314_ = v_toApplicative_1305_;
v_isShared_1315_ = v_isSharedCheck_1335_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_toSeqRight_1312_);
lean_inc(v_toSeqLeft_1311_);
lean_inc(v_toSeq_1310_);
lean_inc(v_toFunctor_1309_);
lean_dec(v_toApplicative_1305_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1335_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___x_1325_; 
v___f_1316_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1317_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1309_);
v___f_1318_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1318_, 0, v_toFunctor_1309_);
v___f_1319_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1319_, 0, v_toFunctor_1309_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___f_1318_);
lean_ctor_set(v___x_1320_, 1, v___f_1319_);
v___f_1321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1321_, 0, v_toSeqRight_1312_);
v___f_1322_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1322_, 0, v_toSeqLeft_1311_);
v___f_1323_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1323_, 0, v_toSeq_1310_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v___f_1321_);
lean_ctor_set(v___x_1314_, 3, v___f_1322_);
lean_ctor_set(v___x_1314_, 2, v___f_1323_);
lean_ctor_set(v___x_1314_, 1, v___f_1316_);
lean_ctor_set(v___x_1314_, 0, v___x_1320_);
v___x_1325_ = v___x_1314_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v___f_1316_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v___f_1323_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v___f_1322_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v___f_1321_);
v___x_1325_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1327_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v___f_1317_);
lean_ctor_set(v___x_1307_, 0, v___x_1325_);
v___x_1327_ = v___x_1307_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___f_1317_);
v___x_1327_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_30893__overap_1331_; lean_object* v___x_1332_; 
v___x_1328_ = l_StateRefT_x27_instMonad___redArg(v___x_1327_);
v___x_1329_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1330_ = l_instInhabitedOfMonad___redArg(v___x_1328_, v___x_1329_);
v___x_30893__overap_1331_ = lean_panic_fn_borrowed(v___x_1330_, v_msg_1272_);
lean_dec(v___x_1330_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
v___x_1332_ = lean_apply_6(v___x_30893__overap_1331_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, lean_box(0));
return v___x_1332_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_msg_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
return v_res_1352_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_toApplicative_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1425_; 
v___x_1361_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1362_ = l_StateRefT_x27_instMonad___redArg(v___x_1361_);
v_toApplicative_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1362_, 1);
lean_dec(v_unused_1426_);
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1425_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_toApplicative_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1425_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_toFunctor_1367_; lean_object* v_toSeq_1368_; lean_object* v_toSeqLeft_1369_; lean_object* v_toSeqRight_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1423_; 
v_toFunctor_1367_ = lean_ctor_get(v_toApplicative_1363_, 0);
v_toSeq_1368_ = lean_ctor_get(v_toApplicative_1363_, 2);
v_toSeqLeft_1369_ = lean_ctor_get(v_toApplicative_1363_, 3);
v_toSeqRight_1370_ = lean_ctor_get(v_toApplicative_1363_, 4);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_toApplicative_1363_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_toApplicative_1363_, 1);
lean_dec(v_unused_1424_);
v___x_1372_ = v_toApplicative_1363_;
v_isShared_1373_ = v_isSharedCheck_1423_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_toSeqRight_1370_);
lean_inc(v_toSeqLeft_1369_);
lean_inc(v_toSeq_1368_);
lean_inc(v_toFunctor_1367_);
lean_dec(v_toApplicative_1363_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1423_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1383_; 
v___f_1374_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1375_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1367_);
v___f_1376_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1376_, 0, v_toFunctor_1367_);
v___f_1377_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1377_, 0, v_toFunctor_1367_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___f_1376_);
lean_ctor_set(v___x_1378_, 1, v___f_1377_);
v___f_1379_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1379_, 0, v_toSeqRight_1370_);
v___f_1380_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1380_, 0, v_toSeqLeft_1369_);
v___f_1381_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1381_, 0, v_toSeq_1368_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 4, v___f_1379_);
lean_ctor_set(v___x_1372_, 3, v___f_1380_);
lean_ctor_set(v___x_1372_, 2, v___f_1381_);
lean_ctor_set(v___x_1372_, 1, v___f_1374_);
lean_ctor_set(v___x_1372_, 0, v___x_1378_);
v___x_1383_ = v___x_1372_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___f_1374_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v___f_1381_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v___f_1380_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v___f_1379_);
v___x_1383_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1385_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___f_1375_);
lean_ctor_set(v___x_1365_, 0, v___x_1383_);
v___x_1385_ = v___x_1365_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___f_1375_);
v___x_1385_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v_toApplicative_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1419_; 
v___x_1386_ = l_StateRefT_x27_instMonad___redArg(v___x_1385_);
v_toApplicative_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1386_, 1);
lean_dec(v_unused_1420_);
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1419_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_toApplicative_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1419_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_toFunctor_1391_; lean_object* v_toSeq_1392_; lean_object* v_toSeqLeft_1393_; lean_object* v_toSeqRight_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1417_; 
v_toFunctor_1391_ = lean_ctor_get(v_toApplicative_1387_, 0);
v_toSeq_1392_ = lean_ctor_get(v_toApplicative_1387_, 2);
v_toSeqLeft_1393_ = lean_ctor_get(v_toApplicative_1387_, 3);
v_toSeqRight_1394_ = lean_ctor_get(v_toApplicative_1387_, 4);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_toApplicative_1387_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_toApplicative_1387_, 1);
lean_dec(v_unused_1418_);
v___x_1396_ = v_toApplicative_1387_;
v_isShared_1397_ = v_isSharedCheck_1417_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_toSeqRight_1394_);
lean_inc(v_toSeqLeft_1393_);
lean_inc(v_toSeq_1392_);
lean_inc(v_toFunctor_1391_);
lean_dec(v_toApplicative_1387_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1417_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___f_1398_; lean_object* v___f_1399_; lean_object* v___f_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___f_1404_; lean_object* v___f_1405_; lean_object* v___x_1407_; 
v___f_1398_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1399_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1391_);
v___f_1400_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1400_, 0, v_toFunctor_1391_);
v___f_1401_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1401_, 0, v_toFunctor_1391_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___f_1400_);
lean_ctor_set(v___x_1402_, 1, v___f_1401_);
v___f_1403_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1403_, 0, v_toSeqRight_1394_);
v___f_1404_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1404_, 0, v_toSeqLeft_1393_);
v___f_1405_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1405_, 0, v_toSeq_1392_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 4, v___f_1403_);
lean_ctor_set(v___x_1396_, 3, v___f_1404_);
lean_ctor_set(v___x_1396_, 2, v___f_1405_);
lean_ctor_set(v___x_1396_, 1, v___f_1398_);
lean_ctor_set(v___x_1396_, 0, v___x_1402_);
v___x_1407_ = v___x_1396_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___f_1398_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v___f_1405_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v___f_1404_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___f_1403_);
v___x_1407_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1409_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v___f_1399_);
lean_ctor_set(v___x_1389_, 0, v___x_1407_);
v___x_1409_ = v___x_1389_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___f_1399_);
v___x_1409_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_30611__overap_1413_; lean_object* v___x_1414_; 
v___x_1410_ = l_StateRefT_x27_instMonad___redArg(v___x_1409_);
v___x_1411_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1412_ = l_instInhabitedOfMonad___redArg(v___x_1410_, v___x_1411_);
v___x_30611__overap_1413_ = lean_panic_fn_borrowed(v___x_1412_, v_msg_1354_);
lean_dec(v___x_1412_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
v___x_1414_ = lean_apply_6(v___x_30611__overap_1413_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, lean_box(0));
return v___x_1414_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1437_ = lean_panic_fn_borrowed(v___x_1436_, v_msg_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1438_, size_t v_i_1439_, lean_object* v_bs_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_usize_dec_lt(v_i_1439_, v_sz_1438_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_bs_1440_);
return v___x_1447_;
}
else
{
lean_object* v_v_1448_; lean_object* v___x_1449_; lean_object* v_bs_x27_1450_; lean_object* v___x_1451_; 
v_v_1448_ = lean_array_uget(v_bs_1440_, v_i_1439_);
v___x_1449_ = lean_unsigned_to_nat(0u);
v_bs_x27_1450_ = lean_array_uset(v_bs_1440_, v_i_1439_, v___x_1449_);
v___x_1451_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1448_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; size_t v___x_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1439_, v___x_1453_);
v___x_1455_ = lean_array_uset(v_bs_x27_1450_, v_i_1439_, v_a_1452_);
v_i_1439_ = v___x_1454_;
v_bs_1440_ = v___x_1455_;
goto _start;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_bs_x27_1450_);
v_a_1457_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1451_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1451_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1465_, lean_object* v_i_1466_, lean_object* v_bs_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1465_);
lean_dec(v_sz_1465_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1466_);
lean_dec(v_i_1466_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1473_, v_i_boxed_1474_, v_bs_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec(v___y_1468_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1478_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1479_ = lean_unsigned_to_nat(66u);
v___x_1480_ = lean_unsigned_to_nat(363u);
v___x_1481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0));
v___x_1482_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1483_ = l_mkPanicMessageWithDecl(v___x_1482_, v___x_1481_, v___x_1480_, v___x_1479_, v___x_1478_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1486_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1487_ = lean_unsigned_to_nat(9u);
v___x_1488_ = lean_unsigned_to_nat(650u);
v___x_1489_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1490_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__2));
v___x_1491_ = l_mkPanicMessageWithDecl(v___x_1490_, v___x_1489_, v___x_1488_, v___x_1487_, v___x_1486_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1492_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1493_ = lean_unsigned_to_nat(27u);
v___x_1494_ = lean_unsigned_to_nat(319u);
v___x_1495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0));
v___x_1496_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1497_ = l_mkPanicMessageWithDecl(v___x_1496_, v___x_1495_, v___x_1494_, v___x_1493_, v___x_1492_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1552_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1553_ = lean_unsigned_to_nat(2u);
v___x_1554_ = lean_unsigned_to_nat(302u);
v___x_1555_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1556_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1557_ = l_mkPanicMessageWithDecl(v___x_1556_, v___x_1555_, v___x_1554_, v___x_1553_, v___x_1552_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1559_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1560_ = lean_unsigned_to_nat(2u);
v___x_1561_ = lean_unsigned_to_nat(304u);
v___x_1562_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1563_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1564_ = l_mkPanicMessageWithDecl(v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_, v___x_1559_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1566_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1567_ = lean_unsigned_to_nat(2u);
v___x_1568_ = lean_unsigned_to_nat(305u);
v___x_1569_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1570_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1571_ = l_mkPanicMessageWithDecl(v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_, v___x_1566_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3(void){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1573_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1574_ = lean_unsigned_to_nat(41u);
v___x_1575_ = lean_unsigned_to_nat(303u);
v___x_1576_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1577_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1578_ = l_mkPanicMessageWithDecl(v___x_1577_, v___x_1576_, v___x_1575_, v___x_1574_, v___x_1573_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1579_, lean_object* v_c_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_discr_1587_; lean_object* v_alts_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1666_; 
v_discr_1587_ = lean_ctor_get(v_c_1580_, 2);
v_alts_1588_ = lean_ctor_get(v_c_1580_, 3);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_c_1580_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; lean_object* v_unused_1668_; 
v_unused_1667_ = lean_ctor_get(v_c_1580_, 1);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_c_1580_, 0);
lean_dec(v_unused_1668_);
v___x_1590_ = v_c_1580_;
v_isShared_1591_ = v_isSharedCheck_1666_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_alts_1588_);
lean_inc(v_discr_1587_);
lean_dec(v_c_1580_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1666_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_array_get_size(v_alts_1588_);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_dec_eq(v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_del_object(v___x_1590_);
lean_dec_ref(v_alts_1588_);
lean_dec(v_discr_1587_);
v___x_1595_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1596_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1595_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_array_get(v___x_1597_, v_alts_1588_, v___x_1598_);
lean_dec_ref(v_alts_1588_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_ctorName_1600_; lean_object* v_params_1601_; lean_object* v_code_1602_; lean_object* v_ctorName_1603_; lean_object* v_fieldIdx_1604_; uint8_t v___x_1605_; 
v_ctorName_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_ctorName_1600_);
v_params_1601_ = lean_ctor_get(v___x_1599_, 1);
lean_inc_ref(v_params_1601_);
v_code_1602_ = lean_ctor_get(v___x_1599_, 2);
lean_inc_ref(v_code_1602_);
lean_dec_ref_known(v___x_1599_, 3);
v_ctorName_1603_ = lean_ctor_get(v_info_1579_, 0);
v_fieldIdx_1604_ = lean_ctor_get(v_info_1579_, 2);
v___x_1605_ = lean_name_eq(v_ctorName_1600_, v_ctorName_1603_);
lean_dec(v_ctorName_1600_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec_ref(v_code_1602_);
lean_dec_ref(v_params_1601_);
lean_del_object(v___x_1590_);
lean_dec(v_discr_1587_);
v___x_1606_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1607_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1606_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = lean_array_get_size(v_params_1601_);
v___x_1609_ = lean_nat_dec_lt(v_fieldIdx_1604_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec_ref(v_code_1602_);
lean_dec_ref(v_params_1601_);
lean_del_object(v___x_1590_);
lean_dec(v_discr_1587_);
v___x_1610_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1611_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1610_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v_p_1614_; lean_object* v___x_1615_; 
v___x_1612_ = 0;
v___x_1613_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v_p_1614_ = lean_array_get(v___x_1613_, v_params_1601_, v_fieldIdx_1604_);
v___x_1615_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1612_, v_params_1601_, v_a_1583_);
lean_dec_ref(v_params_1601_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_fvarId_1616_; lean_object* v_binderName_1617_; lean_object* v_type_1618_; lean_object* v___x_1619_; 
lean_dec_ref_known(v___x_1615_, 1);
v_fvarId_1616_ = lean_ctor_get(v_p_1614_, 0);
lean_inc(v_fvarId_1616_);
v_binderName_1617_ = lean_ctor_get(v_p_1614_, 1);
lean_inc(v_binderName_1617_);
v_type_1618_ = lean_ctor_get(v_p_1614_, 2);
lean_inc_ref(v_type_1618_);
lean_dec(v_p_1614_);
v___x_1619_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1618_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1624_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_1622_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1622_, 0, v_discr_1587_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 3, v___x_1622_);
lean_ctor_set(v___x_1590_, 2, v_a_1620_);
lean_ctor_set(v___x_1590_, 1, v_binderName_1617_);
lean_ctor_set(v___x_1590_, 0, v_fvarId_1616_);
v___x_1624_ = v___x_1590_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_fvarId_1616_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_binderName_1617_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_a_1620_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; lean_object* v_lctx_1626_; lean_object* v_nextIdx_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1646_; 
v___x_1625_ = lean_st_ref_take(v_a_1583_);
v_lctx_1626_ = lean_ctor_get(v___x_1625_, 0);
v_nextIdx_1627_ = lean_ctor_get(v___x_1625_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1629_ = v___x_1625_;
v_isShared_1630_ = v_isSharedCheck_1646_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_nextIdx_1627_);
lean_inc(v_lctx_1626_);
lean_dec(v___x_1625_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1646_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_inc_ref(v___x_1624_);
v___x_1631_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1612_, v_lctx_1626_, v___x_1624_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_nextIdx_1627_);
v___x_1633_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_st_ref_put(v_a_1583_, v___x_1633_);
v___x_1635_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1602_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1624_);
lean_ctor_set(v___x_1640_, 1, v_a_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_dec_ref(v___x_1624_);
return v___x_1635_;
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec(v_binderName_1617_);
lean_dec(v_fvarId_1616_);
lean_dec_ref(v_code_1602_);
lean_del_object(v___x_1590_);
lean_dec(v_discr_1587_);
v_a_1648_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1619_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1619_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_p_1614_);
lean_dec_ref(v_code_1602_);
lean_del_object(v___x_1590_);
lean_dec(v_discr_1587_);
v_a_1656_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1615_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1615_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
lean_dec(v___x_1599_);
lean_del_object(v___x_1590_);
lean_dec(v_discr_1587_);
v___x_1664_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_1665_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1664_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(size_t v_sz_1669_, size_t v_i_1670_, lean_object* v_bs_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v___x_1678_; 
v___x_1678_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1679_, 0, v_bs_1671_);
return v___x_1679_;
}
else
{
lean_object* v_v_1680_; lean_object* v___x_1681_; lean_object* v_bs_x27_1682_; lean_object* v_a_1684_; 
v_v_1680_ = lean_array_uget(v_bs_1671_, v_i_1670_);
v___x_1681_ = lean_unsigned_to_nat(0u);
v_bs_x27_1682_ = lean_array_uset(v_bs_1671_, v_i_1670_, v___x_1681_);
if (lean_obj_tag(v_v_1680_) == 0)
{
lean_object* v_params_1689_; lean_object* v_code_1690_; uint8_t v___x_1691_; size_t v_sz_1692_; size_t v___x_1693_; lean_object* v___x_1694_; 
v_params_1689_ = lean_ctor_get(v_v_1680_, 1);
v_code_1690_ = lean_ctor_get(v_v_1680_, 2);
v___x_1691_ = 0;
v_sz_1692_ = lean_array_size(v_params_1689_);
v___x_1693_ = ((size_t)0ULL);
lean_inc_ref(v_params_1689_);
v___x_1694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1692_, v___x_1693_, v_params_1689_, v___y_1672_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
lean_inc_ref(v_code_1690_);
v___x_1696_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1690_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1691_, v_v_1680_, v_a_1695_, v_a_1697_);
v_a_1684_ = v___x_1698_;
goto v___jp_1683_;
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1695_);
lean_dec_ref_known(v_v_1680_, 3);
lean_dec_ref(v_bs_x27_1682_);
v_a_1699_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1696_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1696_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_1680_, 3);
lean_dec_ref(v_bs_x27_1682_);
return v___x_1694_;
}
}
else
{
lean_object* v_code_1707_; lean_object* v___x_1708_; 
v_code_1707_ = lean_ctor_get(v_v_1680_, 0);
lean_inc_ref(v_code_1707_);
v___x_1708_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1707_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1710_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1680_, v_a_1709_);
v_a_1684_ = v___x_1710_;
goto v___jp_1683_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec_ref_known(v_v_1680_, 1);
lean_dec_ref(v_bs_x27_1682_);
v_a_1711_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1708_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1708_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1670_, v___x_1685_);
v___x_1687_ = lean_array_uset(v_bs_x27_1682_, v_i_1670_, v_a_1684_);
v_i_1670_ = v___x_1686_;
v_bs_1671_ = v___x_1687_;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__1));
v___x_1724_ = lean_unsigned_to_nat(70u);
v___x_1725_ = lean_unsigned_to_nat(373u);
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0));
v___x_1727_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1728_ = l_mkPanicMessageWithDecl(v___x_1727_, v___x_1726_, v___x_1725_, v___x_1724_, v___x_1723_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(lean_object* v___x_1729_, uint8_t v___x_1730_, size_t v_sz_1731_, size_t v_i_1732_, lean_object* v_bs_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_lt(v_i_1732_, v_sz_1731_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref(v___x_1729_);
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_bs_1733_);
return v___x_1741_;
}
else
{
lean_object* v_v_1742_; lean_object* v___x_1743_; lean_object* v_bs_x27_1744_; lean_object* v_a_1746_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; 
v_v_1742_ = lean_array_uget(v_bs_1733_, v_i_1732_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v_bs_x27_1744_ = lean_array_uset(v_bs_1733_, v_i_1732_, v___x_1743_);
if (lean_obj_tag(v_v_1742_) == 0)
{
lean_object* v_ctorName_1768_; lean_object* v_params_1769_; lean_object* v_code_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1808_; 
v_ctorName_1768_ = lean_ctor_get(v_v_1742_, 0);
v_params_1769_ = lean_ctor_get(v_v_1742_, 1);
v_code_1770_ = lean_ctor_get(v_v_1742_, 2);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_v_1742_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1772_ = v_v_1742_;
v_isShared_1773_ = v_isSharedCheck_1808_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_code_1770_);
lean_inc(v_params_1769_);
lean_inc(v_ctorName_1768_);
lean_dec(v_v_1742_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1808_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4));
v___x_1775_ = l_Lean_Name_append(v_ctorName_1768_, v___x_1774_);
lean_inc(v___x_1775_);
lean_inc_ref(v___x_1729_);
v___x_1776_ = l_Lean_Environment_find_x3f(v___x_1729_, v___x_1775_, v___x_1730_);
if (lean_obj_tag(v___x_1776_) == 1)
{
lean_object* v_val_1777_; 
v_val_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_val_1777_);
lean_dec_ref_known(v___x_1776_, 1);
if (lean_obj_tag(v_val_1777_) == 6)
{
lean_object* v_val_1778_; lean_object* v_toConstantVal_1779_; lean_object* v_numParams_1780_; lean_object* v_numFields_1781_; lean_object* v_type_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_val_1778_ = lean_ctor_get(v_val_1777_, 0);
lean_inc_ref(v_val_1778_);
lean_dec_ref_known(v_val_1777_, 1);
v_toConstantVal_1779_ = lean_ctor_get(v_val_1778_, 0);
lean_inc_ref(v_toConstantVal_1779_);
v_numParams_1780_ = lean_ctor_get(v_val_1778_, 3);
lean_inc(v_numParams_1780_);
v_numFields_1781_ = lean_ctor_get(v_val_1778_, 4);
lean_inc(v_numFields_1781_);
lean_dec_ref(v_val_1778_);
v_type_1782_ = lean_ctor_get(v_toConstantVal_1779_, 2);
lean_inc_ref(v_type_1782_);
lean_dec_ref(v_toConstantVal_1779_);
v___x_1783_ = lean_array_get_size(v_params_1769_);
v___x_1784_ = lean_nat_sub(v_numFields_1781_, v___x_1783_);
lean_dec(v_numFields_1781_);
v___x_1785_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_1782_, v_numParams_1780_, v___x_1784_, v_params_1769_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec_ref(v_params_1769_);
lean_dec(v___x_1784_);
lean_dec(v_numParams_1780_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1770_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 2, v_a_1788_);
lean_ctor_set(v___x_1772_, 1, v_a_1786_);
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1790_ = v___x_1772_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_a_1786_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_a_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
v_a_1746_ = v___x_1790_;
goto v___jp_1745_;
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_a_1786_);
lean_dec(v___x_1775_);
lean_del_object(v___x_1772_);
lean_dec_ref(v_bs_x27_1744_);
lean_dec_ref(v___x_1729_);
v_a_1792_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1787_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1787_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v___x_1775_);
lean_del_object(v___x_1772_);
lean_dec_ref(v_code_1770_);
lean_dec_ref(v_bs_x27_1744_);
lean_dec_ref(v___x_1729_);
v_a_1800_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1785_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1785_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_dec(v_val_1777_);
lean_dec(v___x_1775_);
lean_del_object(v___x_1772_);
lean_dec_ref(v_code_1770_);
lean_dec_ref(v_params_1769_);
v___y_1752_ = v___y_1734_;
v___y_1753_ = v___y_1735_;
v___y_1754_ = v___y_1736_;
v___y_1755_ = v___y_1737_;
v___y_1756_ = v___y_1738_;
goto v___jp_1751_;
}
}
else
{
lean_dec(v___x_1776_);
lean_dec(v___x_1775_);
lean_del_object(v___x_1772_);
lean_dec_ref(v_code_1770_);
lean_dec_ref(v_params_1769_);
v___y_1752_ = v___y_1734_;
v___y_1753_ = v___y_1735_;
v___y_1754_ = v___y_1736_;
v___y_1755_ = v___y_1737_;
v___y_1756_ = v___y_1738_;
goto v___jp_1751_;
}
}
}
else
{
lean_object* v_code_1809_; lean_object* v___x_1810_; 
v_code_1809_ = lean_ctor_get(v_v_1742_, 0);
lean_inc_ref(v_code_1809_);
v___x_1810_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1809_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1742_, v_a_1811_);
v_a_1746_ = v___x_1812_;
goto v___jp_1745_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref_known(v_v_1742_, 1);
lean_dec_ref(v_bs_x27_1744_);
lean_dec_ref(v___x_1729_);
v_a_1813_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1810_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1810_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
v___jp_1745_:
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = ((size_t)1ULL);
v___x_1748_ = lean_usize_add(v_i_1732_, v___x_1747_);
v___x_1749_ = lean_array_uset(v_bs_x27_1744_, v_i_1732_, v_a_1746_);
v_i_1732_ = v___x_1748_;
v_bs_1733_ = v___x_1749_;
goto _start;
}
v___jp_1751_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2);
v___x_1758_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_1757_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v_a_1746_ = v_a_1759_;
goto v___jp_1745_;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v_bs_x27_1744_);
lean_dec_ref(v___x_1729_);
v_a_1760_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1758_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1822_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1823_ = lean_unsigned_to_nat(2u);
v___x_1824_ = lean_unsigned_to_nat(291u);
v___x_1825_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1826_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1827_ = l_mkPanicMessageWithDecl(v___x_1826_, v___x_1825_, v___x_1824_, v___x_1823_, v___x_1822_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_unsigned_to_nat(2u);
v___x_1834_ = lean_mk_empty_array_with_capacity(v___x_1833_);
v___x_1835_ = lean_array_push(v___x_1834_, v___x_1832_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1836_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1837_ = lean_unsigned_to_nat(34u);
v___x_1838_ = lean_unsigned_to_nat(292u);
v___x_1839_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1840_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1841_ = l_mkPanicMessageWithDecl(v___x_1840_, v___x_1839_, v___x_1838_, v___x_1837_, v___x_1836_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_discr_1849_; lean_object* v_alts_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1919_; 
v_discr_1849_ = lean_ctor_get(v_c_1842_, 2);
v_alts_1850_ = lean_ctor_get(v_c_1842_, 3);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_c_1842_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1920_ = lean_ctor_get(v_c_1842_, 1);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_c_1842_, 0);
lean_dec(v_unused_1921_);
v___x_1852_ = v_c_1842_;
v_isShared_1853_ = v_isSharedCheck_1919_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_alts_1850_);
lean_inc(v_discr_1849_);
lean_dec(v_c_1842_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1919_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_array_get_size(v_alts_1850_);
v___x_1855_ = lean_unsigned_to_nat(1u);
v___x_1856_ = lean_nat_dec_eq(v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
lean_del_object(v___x_1852_);
lean_dec_ref(v_alts_1850_);
lean_dec(v_discr_1849_);
v___x_1857_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_1858_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1857_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_array_get(v___x_1859_, v_alts_1850_, v___x_1860_);
lean_dec_ref(v_alts_1850_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_params_1862_; lean_object* v_code_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1915_; 
v_params_1862_ = lean_ctor_get(v___x_1861_, 1);
v_code_1863_ = lean_ctor_get(v___x_1861_, 2);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v___x_1861_, 0);
lean_dec(v_unused_1916_);
v___x_1865_ = v___x_1861_;
v_isShared_1866_ = v_isSharedCheck_1915_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_code_1863_);
lean_inc(v_params_1862_);
lean_dec(v___x_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1915_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = 0;
v___x_1868_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1869_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1867_, v_params_1862_, v_a_1845_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1870_; lean_object* v_fvarId_1871_; lean_object* v_binderName_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
lean_dec_ref_known(v___x_1869_, 1);
v___x_1870_ = lean_array_get(v___x_1868_, v_params_1862_, v___x_1860_);
lean_dec_ref(v_params_1862_);
v_fvarId_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_fvarId_1871_);
v_binderName_1872_ = lean_ctor_get(v___x_1870_, 1);
lean_inc(v_binderName_1872_);
lean_dec(v___x_1870_);
v___x_1873_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1874_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_discr_1849_);
v___x_1877_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1878_ = lean_array_push(v___x_1877_, v___x_1876_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set_tag(v___x_1865_, 3);
lean_ctor_set(v___x_1865_, 2, v___x_1878_);
lean_ctor_set(v___x_1865_, 1, v___x_1875_);
lean_ctor_set(v___x_1865_, 0, v___x_1874_);
v___x_1880_ = v___x_1865_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 3, v___x_1880_);
lean_ctor_set(v___x_1852_, 2, v___x_1873_);
lean_ctor_set(v___x_1852_, 1, v_binderName_1872_);
lean_ctor_set(v___x_1852_, 0, v_fvarId_1871_);
v___x_1882_ = v___x_1852_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_fvarId_1871_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_binderName_1872_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v_lctx_1884_; lean_object* v_nextIdx_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1904_; 
v___x_1883_ = lean_st_ref_take(v_a_1845_);
v_lctx_1884_ = lean_ctor_get(v___x_1883_, 0);
v_nextIdx_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1904_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_nextIdx_1885_);
lean_inc(v_lctx_1884_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1904_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_inc_ref(v___x_1882_);
v___x_1889_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1867_, v_lctx_1884_, v___x_1882_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1889_);
v___x_1891_ = v___x_1887_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_nextIdx_1885_);
v___x_1891_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_st_ref_put(v_a_1845_, v___x_1891_);
v___x_1893_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1863_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1902_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1902_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1882_);
lean_ctor_set(v___x_1898_, 1, v_a_1894_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1898_);
v___x_1900_ = v___x_1896_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
else
{
lean_dec_ref(v___x_1882_);
return v___x_1893_;
}
}
}
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_del_object(v___x_1865_);
lean_dec_ref(v_code_1863_);
lean_dec_ref(v_params_1862_);
lean_del_object(v___x_1852_);
lean_dec(v_discr_1849_);
v_a_1907_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1869_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1869_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec(v___x_1861_);
lean_del_object(v___x_1852_);
lean_dec(v_discr_1849_);
v___x_1917_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_1918_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1917_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_);
return v___x_1918_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1923_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1924_ = lean_unsigned_to_nat(2u);
v___x_1925_ = lean_unsigned_to_nat(271u);
v___x_1926_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1927_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1928_ = l_mkPanicMessageWithDecl(v___x_1927_, v___x_1926_, v___x_1925_, v___x_1924_, v___x_1923_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_box(0);
v___x_1936_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_1937_ = l_Lean_Expr_const___override(v___x_1936_, v___x_1935_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1938_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1939_ = lean_unsigned_to_nat(34u);
v___x_1940_ = lean_unsigned_to_nat(272u);
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1942_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1943_ = l_mkPanicMessageWithDecl(v___x_1942_, v___x_1941_, v___x_1940_, v___x_1939_, v___x_1938_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_discr_1951_; lean_object* v_alts_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v_discr_1951_ = lean_ctor_get(v_c_1944_, 2);
v_alts_1952_ = lean_ctor_get(v_c_1944_, 3);
v___x_1953_ = lean_array_get_size(v_alts_1952_);
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_dec_eq(v___x_1953_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_1957_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1956_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1957_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_array_get(v___x_1958_, v_alts_1952_, v___x_1959_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_params_1961_; lean_object* v_code_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2060_; 
v_params_1961_ = lean_ctor_get(v___x_1960_, 1);
v_code_1962_ = lean_ctor_get(v___x_1960_, 2);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v___x_1960_, 0);
lean_dec(v_unused_2061_);
v___x_1964_ = v___x_1960_;
v_isShared_1965_ = v_isSharedCheck_2060_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_code_1962_);
lean_inc(v_params_1961_);
lean_dec(v___x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2060_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = 0;
v___x_1967_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1968_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1966_, v_params_1961_, v_a_1947_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_dec_ref_known(v___x_1968_, 1);
v___x_1969_ = lean_array_get(v___x_1967_, v_params_1961_, v___x_1959_);
lean_dec_ref(v_params_1961_);
v___x_1970_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_1971_ = lean_box(0);
lean_inc(v_discr_1951_);
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v_discr_1951_);
v___x_1973_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1974_ = lean_array_push(v___x_1973_, v___x_1972_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set_tag(v___x_1964_, 3);
lean_ctor_set(v___x_1964_, 2, v___x_1974_);
lean_ctor_set(v___x_1964_, 1, v___x_1971_);
lean_ctor_set(v___x_1964_, 0, v___x_1970_);
v___x_1976_ = v___x_1964_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_1971_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_2051_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_1978_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1977_, v_a_1947_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___x_1980_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1981_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1966_, v_a_1979_, v___x_1980_, v___x_1976_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___x_1985_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_1984_ = 0;
v___x_1985_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_1966_, v___x_1983_, v___x_1984_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; lean_object* v___x_1987_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_1987_ = l_Lean_mkArrow(v___x_1983_, v___x_1980_, v_a_1948_, v_a_1949_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v_fvarId_1989_; lean_object* v_binderName_1990_; lean_object* v_fvarId_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_lctx_1998_; lean_object* v_nextIdx_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2018_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v_fvarId_1989_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_fvarId_1989_);
v_binderName_1990_ = lean_ctor_get(v___x_1969_, 1);
lean_inc(v_binderName_1990_);
lean_dec(v___x_1969_);
v_fvarId_1991_ = lean_ctor_get(v_a_1982_, 0);
v___x_1992_ = lean_mk_empty_array_with_capacity(v___x_1954_);
v___x_1993_ = lean_array_push(v___x_1992_, v_a_1986_);
lean_inc(v_fvarId_1991_);
v___x_1994_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_fvarId_1991_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_a_1982_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1996_, 0, v_fvarId_1989_);
lean_ctor_set(v___x_1996_, 1, v_binderName_1990_);
lean_ctor_set(v___x_1996_, 2, v___x_1993_);
lean_ctor_set(v___x_1996_, 3, v_a_1988_);
lean_ctor_set(v___x_1996_, 4, v___x_1995_);
v___x_1997_ = lean_st_ref_take(v_a_1947_);
v_lctx_1998_ = lean_ctor_get(v___x_1997_, 0);
v_nextIdx_1999_ = lean_ctor_get(v___x_1997_, 1);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2001_ = v___x_1997_;
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_nextIdx_1999_);
lean_inc(v_lctx_1998_);
lean_dec(v___x_1997_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2018_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
lean_inc_ref(v___x_1996_);
v___x_2003_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_1966_, v_lctx_1998_, v___x_1996_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_nextIdx_1999_);
v___x_2005_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_st_ref_put(v_a_1947_, v___x_2005_);
v___x_2007_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1962_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
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
v___x_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_1996_);
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
lean_dec_ref_known(v___x_1996_, 5);
return v___x_2007_;
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_a_1986_);
lean_dec(v_a_1982_);
lean_dec(v___x_1969_);
lean_dec_ref(v_code_1962_);
v_a_2019_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1987_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1987_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_a_1982_);
lean_dec(v___x_1969_);
lean_dec_ref(v_code_1962_);
v_a_2027_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1985_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1985_);
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
lean_dec(v___x_1969_);
lean_dec_ref(v_code_1962_);
v_a_2035_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1981_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1981_);
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
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___x_1976_);
lean_dec(v___x_1969_);
lean_dec_ref(v_code_1962_);
v_a_2043_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_1978_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_1978_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_del_object(v___x_1964_);
lean_dec_ref(v_code_1962_);
lean_dec_ref(v_params_1961_);
v_a_2052_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1968_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1968_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v___x_1960_);
v___x_2062_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2063_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2062_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_2063_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2065_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2066_ = lean_unsigned_to_nat(2u);
v___x_2067_ = lean_unsigned_to_nat(260u);
v___x_2068_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2069_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2070_ = l_mkPanicMessageWithDecl(v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_, v___x_2065_);
return v___x_2070_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2076_ = lean_unsigned_to_nat(34u);
v___x_2077_ = lean_unsigned_to_nat(261u);
v___x_2078_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2079_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2080_ = l_mkPanicMessageWithDecl(v___x_2079_, v___x_2078_, v___x_2077_, v___x_2076_, v___x_2075_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_discr_2088_; lean_object* v_alts_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2158_; 
v_discr_2088_ = lean_ctor_get(v_c_2081_, 2);
v_alts_2089_ = lean_ctor_get(v_c_2081_, 3);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_c_2081_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; 
v_unused_2159_ = lean_ctor_get(v_c_2081_, 1);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_c_2081_, 0);
lean_dec(v_unused_2160_);
v___x_2091_ = v_c_2081_;
v_isShared_2092_ = v_isSharedCheck_2158_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_alts_2089_);
lean_inc(v_discr_2088_);
lean_dec(v_c_2081_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2158_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2093_ = lean_array_get_size(v_alts_2089_);
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_dec_eq(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
lean_del_object(v___x_2091_);
lean_dec_ref(v_alts_2089_);
lean_dec(v_discr_2088_);
v___x_2096_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2097_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2096_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
return v___x_2097_;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = lean_array_get(v___x_2098_, v_alts_2089_, v___x_2099_);
lean_dec_ref(v_alts_2089_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_params_2101_; lean_object* v_code_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2154_; 
v_params_2101_ = lean_ctor_get(v___x_2100_, 1);
v_code_2102_ = lean_ctor_get(v___x_2100_, 2);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v___x_2100_, 0);
lean_dec(v_unused_2155_);
v___x_2104_ = v___x_2100_;
v_isShared_2105_ = v_isSharedCheck_2154_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_code_2102_);
lean_inc(v_params_2101_);
lean_dec(v___x_2100_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2154_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = 0;
v___x_2107_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2108_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2106_, v_params_2101_, v_a_2084_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v___x_2109_; lean_object* v_fvarId_2110_; lean_object* v_binderName_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec_ref_known(v___x_2108_, 1);
v___x_2109_ = lean_array_get(v___x_2107_, v_params_2101_, v___x_2099_);
lean_dec_ref(v_params_2101_);
v_fvarId_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_fvarId_2110_);
v_binderName_2111_ = lean_ctor_get(v___x_2109_, 1);
lean_inc(v_binderName_2111_);
lean_dec(v___x_2109_);
v___x_2112_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2113_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v_discr_2088_);
v___x_2116_ = lean_mk_empty_array_with_capacity(v___x_2094_);
v___x_2117_ = lean_array_push(v___x_2116_, v___x_2115_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set_tag(v___x_2104_, 3);
lean_ctor_set(v___x_2104_, 2, v___x_2117_);
lean_ctor_set(v___x_2104_, 1, v___x_2114_);
lean_ctor_set(v___x_2104_, 0, v___x_2113_);
v___x_2119_ = v___x_2104_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2114_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2121_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 3, v___x_2119_);
lean_ctor_set(v___x_2091_, 2, v___x_2112_);
lean_ctor_set(v___x_2091_, 1, v_binderName_2111_);
lean_ctor_set(v___x_2091_, 0, v_fvarId_2110_);
v___x_2121_ = v___x_2091_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_fvarId_2110_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_binderName_2111_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v_lctx_2123_; lean_object* v_nextIdx_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2143_; 
v___x_2122_ = lean_st_ref_take(v_a_2084_);
v_lctx_2123_ = lean_ctor_get(v___x_2122_, 0);
v_nextIdx_2124_ = lean_ctor_get(v___x_2122_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2143_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_nextIdx_2124_);
lean_inc(v_lctx_2123_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2143_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_inc_ref(v___x_2121_);
v___x_2128_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2106_, v_lctx_2123_, v___x_2121_);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2128_);
v___x_2130_ = v___x_2126_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_nextIdx_2124_);
v___x_2130_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = lean_st_ref_put(v_a_2084_, v___x_2130_);
v___x_2132_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2102_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2141_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2135_ = v___x_2132_;
v_isShared_2136_ = v_isSharedCheck_2141_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2141_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2121_);
lean_ctor_set(v___x_2137_, 1, v_a_2133_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
else
{
lean_dec_ref(v___x_2121_);
return v___x_2132_;
}
}
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_del_object(v___x_2104_);
lean_dec_ref(v_code_2102_);
lean_dec_ref(v_params_2101_);
lean_del_object(v___x_2091_);
lean_dec(v_discr_2088_);
v_a_2146_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2108_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2108_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
lean_dec(v___x_2100_);
lean_del_object(v___x_2091_);
lean_dec(v_discr_2088_);
v___x_2156_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2157_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2156_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
return v___x_2157_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2163_ = lean_unsigned_to_nat(2u);
v___x_2164_ = lean_unsigned_to_nat(249u);
v___x_2165_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2166_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2167_ = l_mkPanicMessageWithDecl(v___x_2166_, v___x_2165_, v___x_2164_, v___x_2163_, v___x_2162_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2171_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2172_ = lean_unsigned_to_nat(34u);
v___x_2173_ = lean_unsigned_to_nat(250u);
v___x_2174_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2175_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2176_ = l_mkPanicMessageWithDecl(v___x_2175_, v___x_2174_, v___x_2173_, v___x_2172_, v___x_2171_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_discr_2184_; lean_object* v_alts_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2254_; 
v_discr_2184_ = lean_ctor_get(v_c_2177_, 2);
v_alts_2185_ = lean_ctor_get(v_c_2177_, 3);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_c_2177_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; lean_object* v_unused_2256_; 
v_unused_2255_ = lean_ctor_get(v_c_2177_, 1);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_c_2177_, 0);
lean_dec(v_unused_2256_);
v___x_2187_ = v_c_2177_;
v_isShared_2188_ = v_isSharedCheck_2254_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_alts_2185_);
lean_inc(v_discr_2184_);
lean_dec(v_c_2177_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2254_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = lean_array_get_size(v_alts_2185_);
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_nat_dec_eq(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_del_object(v___x_2187_);
lean_dec_ref(v_alts_2185_);
lean_dec(v_discr_2184_);
v___x_2192_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2193_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2192_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = lean_array_get(v___x_2194_, v_alts_2185_, v___x_2195_);
lean_dec_ref(v_alts_2185_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_params_2197_; lean_object* v_code_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2250_; 
v_params_2197_ = lean_ctor_get(v___x_2196_, 1);
v_code_2198_ = lean_ctor_get(v___x_2196_, 2);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; 
v_unused_2251_ = lean_ctor_get(v___x_2196_, 0);
lean_dec(v_unused_2251_);
v___x_2200_ = v___x_2196_;
v_isShared_2201_ = v_isSharedCheck_2250_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_code_2198_);
lean_inc(v_params_2197_);
lean_dec(v___x_2196_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2250_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = 0;
v___x_2203_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2204_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2202_, v_params_2197_, v_a_2180_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2205_; lean_object* v_fvarId_2206_; lean_object* v_binderName_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec_ref_known(v___x_2204_, 1);
v___x_2205_ = lean_array_get(v___x_2203_, v_params_2197_, v___x_2195_);
lean_dec_ref(v_params_2197_);
v_fvarId_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_fvarId_2206_);
v_binderName_2207_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_binderName_2207_);
lean_dec(v___x_2205_);
v___x_2208_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2209_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_discr_2184_);
v___x_2212_ = lean_mk_empty_array_with_capacity(v___x_2190_);
v___x_2213_ = lean_array_push(v___x_2212_, v___x_2211_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set_tag(v___x_2200_, 3);
lean_ctor_set(v___x_2200_, 2, v___x_2213_);
lean_ctor_set(v___x_2200_, 1, v___x_2210_);
lean_ctor_set(v___x_2200_, 0, v___x_2209_);
v___x_2215_ = v___x_2200_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2209_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2210_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 3, v___x_2215_);
lean_ctor_set(v___x_2187_, 2, v___x_2208_);
lean_ctor_set(v___x_2187_, 1, v_binderName_2207_);
lean_ctor_set(v___x_2187_, 0, v_fvarId_2206_);
v___x_2217_ = v___x_2187_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_fvarId_2206_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v_binderName_2207_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2240_, 3, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v_lctx_2219_; lean_object* v_nextIdx_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2239_; 
v___x_2218_ = lean_st_ref_take(v_a_2180_);
v_lctx_2219_ = lean_ctor_get(v___x_2218_, 0);
v_nextIdx_2220_ = lean_ctor_get(v___x_2218_, 1);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2222_ = v___x_2218_;
v_isShared_2223_ = v_isSharedCheck_2239_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_nextIdx_2220_);
lean_inc(v_lctx_2219_);
lean_dec(v___x_2218_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2239_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
lean_inc_ref(v___x_2217_);
v___x_2224_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2202_, v_lctx_2219_, v___x_2217_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_nextIdx_2220_);
v___x_2226_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_st_ref_put(v_a_2180_, v___x_2226_);
v___x_2228_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2198_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2217_);
lean_ctor_set(v___x_2233_, 1, v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_dec_ref(v___x_2217_);
return v___x_2228_;
}
}
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_del_object(v___x_2200_);
lean_dec_ref(v_code_2198_);
lean_dec_ref(v_params_2197_);
lean_del_object(v___x_2187_);
lean_dec(v_discr_2184_);
v_a_2242_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2204_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2204_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v___x_2196_);
lean_del_object(v___x_2187_);
lean_dec(v_discr_2184_);
v___x_2252_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2253_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2252_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
return v___x_2253_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2258_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2259_ = lean_unsigned_to_nat(2u);
v___x_2260_ = lean_unsigned_to_nat(238u);
v___x_2261_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2262_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2263_ = l_mkPanicMessageWithDecl(v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2268_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2269_ = lean_unsigned_to_nat(34u);
v___x_2270_ = lean_unsigned_to_nat(239u);
v___x_2271_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2272_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2273_ = l_mkPanicMessageWithDecl(v___x_2272_, v___x_2271_, v___x_2270_, v___x_2269_, v___x_2268_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_discr_2281_; lean_object* v_alts_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2351_; 
v_discr_2281_ = lean_ctor_get(v_c_2274_, 2);
v_alts_2282_ = lean_ctor_get(v_c_2274_, 3);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_c_2274_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; lean_object* v_unused_2353_; 
v_unused_2352_ = lean_ctor_get(v_c_2274_, 1);
lean_dec(v_unused_2352_);
v_unused_2353_ = lean_ctor_get(v_c_2274_, 0);
lean_dec(v_unused_2353_);
v___x_2284_ = v_c_2274_;
v_isShared_2285_ = v_isSharedCheck_2351_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_alts_2282_);
lean_inc(v_discr_2281_);
lean_dec(v_c_2274_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2351_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2286_ = lean_array_get_size(v_alts_2282_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_dec_eq(v___x_2286_, v___x_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_del_object(v___x_2284_);
lean_dec_ref(v_alts_2282_);
lean_dec(v_discr_2281_);
v___x_2289_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2290_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2289_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2292_ = lean_unsigned_to_nat(0u);
v___x_2293_ = lean_array_get(v___x_2291_, v_alts_2282_, v___x_2292_);
lean_dec_ref(v_alts_2282_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_params_2294_; lean_object* v_code_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2347_; 
v_params_2294_ = lean_ctor_get(v___x_2293_, 1);
v_code_2295_ = lean_ctor_get(v___x_2293_, 2);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v___x_2293_, 0);
lean_dec(v_unused_2348_);
v___x_2297_ = v___x_2293_;
v_isShared_2298_ = v_isSharedCheck_2347_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_code_2295_);
lean_inc(v_params_2294_);
lean_dec(v___x_2293_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2347_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = 0;
v___x_2300_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2301_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2299_, v_params_2294_, v_a_2277_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v___x_2302_; lean_object* v_fvarId_2303_; lean_object* v_binderName_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_dec_ref_known(v___x_2301_, 1);
v___x_2302_ = lean_array_get(v___x_2300_, v_params_2294_, v___x_2292_);
lean_dec_ref(v_params_2294_);
v_fvarId_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_fvarId_2303_);
v_binderName_2304_ = lean_ctor_get(v___x_2302_, 1);
lean_inc(v_binderName_2304_);
lean_dec(v___x_2302_);
v___x_2305_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2306_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2307_ = lean_box(0);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_discr_2281_);
v___x_2309_ = lean_mk_empty_array_with_capacity(v___x_2287_);
v___x_2310_ = lean_array_push(v___x_2309_, v___x_2308_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set_tag(v___x_2297_, 3);
lean_ctor_set(v___x_2297_, 2, v___x_2310_);
lean_ctor_set(v___x_2297_, 1, v___x_2307_);
lean_ctor_set(v___x_2297_, 0, v___x_2306_);
v___x_2312_ = v___x_2297_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 3, v___x_2312_);
lean_ctor_set(v___x_2284_, 2, v___x_2305_);
lean_ctor_set(v___x_2284_, 1, v_binderName_2304_);
lean_ctor_set(v___x_2284_, 0, v_fvarId_2303_);
v___x_2314_ = v___x_2284_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_fvarId_2303_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_binderName_2304_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2337_, 3, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v_lctx_2316_; lean_object* v_nextIdx_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2336_; 
v___x_2315_ = lean_st_ref_take(v_a_2277_);
v_lctx_2316_ = lean_ctor_get(v___x_2315_, 0);
v_nextIdx_2317_ = lean_ctor_get(v___x_2315_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2319_ = v___x_2315_;
v_isShared_2320_ = v_isSharedCheck_2336_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_nextIdx_2317_);
lean_inc(v_lctx_2316_);
lean_dec(v___x_2315_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2336_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
lean_inc_ref(v___x_2314_);
v___x_2321_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2299_, v_lctx_2316_, v___x_2314_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v___x_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_nextIdx_2317_);
v___x_2323_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_st_ref_put(v_a_2277_, v___x_2323_);
v___x_2325_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2295_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2334_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2334_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2332_; 
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2314_);
lean_ctor_set(v___x_2330_, 1, v_a_2326_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2330_);
v___x_2332_ = v___x_2328_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
else
{
lean_dec_ref(v___x_2314_);
return v___x_2325_;
}
}
}
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_del_object(v___x_2297_);
lean_dec_ref(v_code_2295_);
lean_dec_ref(v_params_2294_);
lean_del_object(v___x_2284_);
lean_dec(v_discr_2281_);
v_a_2339_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2301_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2301_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v___x_2293_);
lean_del_object(v___x_2284_);
lean_dec(v_discr_2281_);
v___x_2349_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2350_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2349_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2350_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2355_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2356_ = lean_unsigned_to_nat(2u);
v___x_2357_ = lean_unsigned_to_nat(227u);
v___x_2358_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2359_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2360_ = l_mkPanicMessageWithDecl(v___x_2359_, v___x_2358_, v___x_2357_, v___x_2356_, v___x_2355_);
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2365_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2366_ = lean_unsigned_to_nat(34u);
v___x_2367_ = lean_unsigned_to_nat(228u);
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2369_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2370_ = l_mkPanicMessageWithDecl(v___x_2369_, v___x_2368_, v___x_2367_, v___x_2366_, v___x_2365_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_discr_2378_; lean_object* v_alts_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2448_; 
v_discr_2378_ = lean_ctor_get(v_c_2371_, 2);
v_alts_2379_ = lean_ctor_get(v_c_2371_, 3);
v_isSharedCheck_2448_ = !lean_is_exclusive(v_c_2371_);
if (v_isSharedCheck_2448_ == 0)
{
lean_object* v_unused_2449_; lean_object* v_unused_2450_; 
v_unused_2449_ = lean_ctor_get(v_c_2371_, 1);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_c_2371_, 0);
lean_dec(v_unused_2450_);
v___x_2381_ = v_c_2371_;
v_isShared_2382_ = v_isSharedCheck_2448_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_alts_2379_);
lean_inc(v_discr_2378_);
lean_dec(v_c_2371_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2448_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2383_ = lean_array_get_size(v_alts_2379_);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_nat_dec_eq(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
lean_del_object(v___x_2381_);
lean_dec_ref(v_alts_2379_);
lean_dec(v_discr_2378_);
v___x_2386_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2387_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2386_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2387_;
}
else
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_array_get(v___x_2388_, v_alts_2379_, v___x_2389_);
lean_dec_ref(v_alts_2379_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_params_2391_; lean_object* v_code_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2444_; 
v_params_2391_ = lean_ctor_get(v___x_2390_, 1);
v_code_2392_ = lean_ctor_get(v___x_2390_, 2);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; 
v_unused_2445_ = lean_ctor_get(v___x_2390_, 0);
lean_dec(v_unused_2445_);
v___x_2394_ = v___x_2390_;
v_isShared_2395_ = v_isSharedCheck_2444_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_code_2392_);
lean_inc(v_params_2391_);
lean_dec(v___x_2390_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2444_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = 0;
v___x_2397_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2398_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2396_, v_params_2391_, v_a_2374_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; lean_object* v_fvarId_2400_; lean_object* v_binderName_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec_ref_known(v___x_2398_, 1);
v___x_2399_ = lean_array_get(v___x_2397_, v_params_2391_, v___x_2389_);
lean_dec_ref(v_params_2391_);
v_fvarId_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_fvarId_2400_);
v_binderName_2401_ = lean_ctor_get(v___x_2399_, 1);
lean_inc(v_binderName_2401_);
lean_dec(v___x_2399_);
v___x_2402_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2403_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2405_, 0, v_discr_2378_);
v___x_2406_ = lean_mk_empty_array_with_capacity(v___x_2384_);
v___x_2407_ = lean_array_push(v___x_2406_, v___x_2405_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 3);
lean_ctor_set(v___x_2394_, 2, v___x_2407_);
lean_ctor_set(v___x_2394_, 1, v___x_2404_);
lean_ctor_set(v___x_2394_, 0, v___x_2403_);
v___x_2409_ = v___x_2394_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 3, v___x_2409_);
lean_ctor_set(v___x_2381_, 2, v___x_2402_);
lean_ctor_set(v___x_2381_, 1, v_binderName_2401_);
lean_ctor_set(v___x_2381_, 0, v_fvarId_2400_);
v___x_2411_ = v___x_2381_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_fvarId_2400_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v_binderName_2401_);
lean_ctor_set(v_reuseFailAlloc_2434_, 2, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2434_, 3, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v_lctx_2413_; lean_object* v_nextIdx_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2433_; 
v___x_2412_ = lean_st_ref_take(v_a_2374_);
v_lctx_2413_ = lean_ctor_get(v___x_2412_, 0);
v_nextIdx_2414_ = lean_ctor_get(v___x_2412_, 1);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2416_ = v___x_2412_;
v_isShared_2417_ = v_isSharedCheck_2433_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_nextIdx_2414_);
lean_inc(v_lctx_2413_);
lean_dec(v___x_2412_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2433_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
lean_inc_ref(v___x_2411_);
v___x_2418_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2396_, v_lctx_2413_, v___x_2411_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2418_);
v___x_2420_ = v___x_2416_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_nextIdx_2414_);
v___x_2420_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_st_ref_put(v_a_2374_, v___x_2420_);
v___x_2422_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2392_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2431_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2431_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2411_);
lean_ctor_set(v___x_2427_, 1, v_a_2423_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
else
{
lean_dec_ref(v___x_2411_);
return v___x_2422_;
}
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_del_object(v___x_2394_);
lean_dec_ref(v_code_2392_);
lean_dec_ref(v_params_2391_);
lean_del_object(v___x_2381_);
lean_dec(v_discr_2378_);
v_a_2436_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2398_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2398_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v___x_2390_);
lean_del_object(v___x_2381_);
lean_dec(v_discr_2378_);
v___x_2446_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2447_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2446_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2447_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2452_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2453_ = lean_unsigned_to_nat(2u);
v___x_2454_ = lean_unsigned_to_nat(215u);
v___x_2455_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2456_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2457_ = l_mkPanicMessageWithDecl(v___x_2456_, v___x_2455_, v___x_2454_, v___x_2453_, v___x_2452_);
return v___x_2457_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2461_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2462_ = lean_unsigned_to_nat(34u);
v___x_2463_ = lean_unsigned_to_nat(216u);
v___x_2464_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2465_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2466_ = l_mkPanicMessageWithDecl(v___x_2465_, v___x_2464_, v___x_2463_, v___x_2462_, v___x_2461_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v_discr_2474_; lean_object* v_alts_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2544_; 
v_discr_2474_ = lean_ctor_get(v_c_2467_, 2);
v_alts_2475_ = lean_ctor_get(v_c_2467_, 3);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_c_2467_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; lean_object* v_unused_2546_; 
v_unused_2545_ = lean_ctor_get(v_c_2467_, 1);
lean_dec(v_unused_2545_);
v_unused_2546_ = lean_ctor_get(v_c_2467_, 0);
lean_dec(v_unused_2546_);
v___x_2477_ = v_c_2467_;
v_isShared_2478_ = v_isSharedCheck_2544_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_alts_2475_);
lean_inc(v_discr_2474_);
lean_dec(v_c_2467_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2544_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2479_ = lean_array_get_size(v_alts_2475_);
v___x_2480_ = lean_unsigned_to_nat(1u);
v___x_2481_ = lean_nat_dec_eq(v___x_2479_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_del_object(v___x_2477_);
lean_dec_ref(v_alts_2475_);
lean_dec(v_discr_2474_);
v___x_2482_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2483_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2482_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2485_ = lean_unsigned_to_nat(0u);
v___x_2486_ = lean_array_get(v___x_2484_, v_alts_2475_, v___x_2485_);
lean_dec_ref(v_alts_2475_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_params_2487_; lean_object* v_code_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2540_; 
v_params_2487_ = lean_ctor_get(v___x_2486_, 1);
v_code_2488_ = lean_ctor_get(v___x_2486_, 2);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2486_, 0);
lean_dec(v_unused_2541_);
v___x_2490_ = v___x_2486_;
v_isShared_2491_ = v_isSharedCheck_2540_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_code_2488_);
lean_inc(v_params_2487_);
lean_dec(v___x_2486_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2540_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
uint8_t v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = 0;
v___x_2493_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2494_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2492_, v_params_2487_, v_a_2470_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v___x_2495_; lean_object* v_fvarId_2496_; lean_object* v_binderName_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
lean_dec_ref_known(v___x_2494_, 1);
v___x_2495_ = lean_array_get(v___x_2493_, v_params_2487_, v___x_2485_);
lean_dec_ref(v_params_2487_);
v_fvarId_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_fvarId_2496_);
v_binderName_2497_ = lean_ctor_get(v___x_2495_, 1);
lean_inc(v_binderName_2497_);
lean_dec(v___x_2495_);
v___x_2498_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2499_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2501_, 0, v_discr_2474_);
v___x_2502_ = lean_mk_empty_array_with_capacity(v___x_2480_);
v___x_2503_ = lean_array_push(v___x_2502_, v___x_2501_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set_tag(v___x_2490_, 3);
lean_ctor_set(v___x_2490_, 2, v___x_2503_);
lean_ctor_set(v___x_2490_, 1, v___x_2500_);
lean_ctor_set(v___x_2490_, 0, v___x_2499_);
v___x_2505_ = v___x_2490_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 3, v___x_2505_);
lean_ctor_set(v___x_2477_, 2, v___x_2498_);
lean_ctor_set(v___x_2477_, 1, v_binderName_2497_);
lean_ctor_set(v___x_2477_, 0, v_fvarId_2496_);
v___x_2507_ = v___x_2477_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_fvarId_2496_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_binderName_2497_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v_lctx_2509_; lean_object* v_nextIdx_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2529_; 
v___x_2508_ = lean_st_ref_take(v_a_2470_);
v_lctx_2509_ = lean_ctor_get(v___x_2508_, 0);
v_nextIdx_2510_ = lean_ctor_get(v___x_2508_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2512_ = v___x_2508_;
v_isShared_2513_ = v_isSharedCheck_2529_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_nextIdx_2510_);
lean_inc(v_lctx_2509_);
lean_dec(v___x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2529_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2514_; lean_object* v___x_2516_; 
lean_inc_ref(v___x_2507_);
v___x_2514_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2492_, v_lctx_2509_, v___x_2507_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2514_);
v___x_2516_ = v___x_2512_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_nextIdx_2510_);
v___x_2516_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_st_ref_put(v_a_2470_, v___x_2516_);
v___x_2518_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2488_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2527_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2507_);
lean_ctor_set(v___x_2523_, 1, v_a_2519_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_dec_ref(v___x_2507_);
return v___x_2518_;
}
}
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_del_object(v___x_2490_);
lean_dec_ref(v_code_2488_);
lean_dec_ref(v_params_2487_);
lean_del_object(v___x_2477_);
lean_dec(v_discr_2474_);
v_a_2532_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2494_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2494_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec(v___x_2486_);
lean_del_object(v___x_2477_);
lean_dec(v_discr_2474_);
v___x_2542_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2543_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2542_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
return v___x_2543_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2548_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2549_ = lean_unsigned_to_nat(2u);
v___x_2550_ = lean_unsigned_to_nat(203u);
v___x_2551_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2552_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2553_ = l_mkPanicMessageWithDecl(v___x_2552_, v___x_2551_, v___x_2550_, v___x_2549_, v___x_2548_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2558_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2559_ = lean_unsigned_to_nat(34u);
v___x_2560_ = lean_unsigned_to_nat(204u);
v___x_2561_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2562_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2563_ = l_mkPanicMessageWithDecl(v___x_2562_, v___x_2561_, v___x_2560_, v___x_2559_, v___x_2558_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v_discr_2571_; lean_object* v_alts_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2641_; 
v_discr_2571_ = lean_ctor_get(v_c_2564_, 2);
v_alts_2572_ = lean_ctor_get(v_c_2564_, 3);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_c_2564_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; lean_object* v_unused_2643_; 
v_unused_2642_ = lean_ctor_get(v_c_2564_, 1);
lean_dec(v_unused_2642_);
v_unused_2643_ = lean_ctor_get(v_c_2564_, 0);
lean_dec(v_unused_2643_);
v___x_2574_ = v_c_2564_;
v_isShared_2575_ = v_isSharedCheck_2641_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_alts_2572_);
lean_inc(v_discr_2571_);
lean_dec(v_c_2564_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2641_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_array_get_size(v_alts_2572_);
v___x_2577_ = lean_unsigned_to_nat(1u);
v___x_2578_ = lean_nat_dec_eq(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_del_object(v___x_2574_);
lean_dec_ref(v_alts_2572_);
lean_dec(v_discr_2571_);
v___x_2579_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2580_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2579_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
return v___x_2580_;
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2582_ = lean_unsigned_to_nat(0u);
v___x_2583_ = lean_array_get(v___x_2581_, v_alts_2572_, v___x_2582_);
lean_dec_ref(v_alts_2572_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_params_2584_; lean_object* v_code_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2637_; 
v_params_2584_ = lean_ctor_get(v___x_2583_, 1);
v_code_2585_ = lean_ctor_get(v___x_2583_, 2);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2637_ == 0)
{
lean_object* v_unused_2638_; 
v_unused_2638_ = lean_ctor_get(v___x_2583_, 0);
lean_dec(v_unused_2638_);
v___x_2587_ = v___x_2583_;
v_isShared_2588_ = v_isSharedCheck_2637_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_code_2585_);
lean_inc(v_params_2584_);
lean_dec(v___x_2583_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2637_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = 0;
v___x_2590_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2591_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2589_, v_params_2584_, v_a_2567_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; lean_object* v_fvarId_2593_; lean_object* v_binderName_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec_ref_known(v___x_2591_, 1);
v___x_2592_ = lean_array_get(v___x_2590_, v_params_2584_, v___x_2582_);
lean_dec_ref(v_params_2584_);
v_fvarId_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_fvarId_2593_);
v_binderName_2594_ = lean_ctor_get(v___x_2592_, 1);
lean_inc(v_binderName_2594_);
lean_dec(v___x_2592_);
v___x_2595_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2596_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2597_ = lean_box(0);
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v_discr_2571_);
v___x_2599_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2600_ = lean_array_push(v___x_2599_, v___x_2598_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 3);
lean_ctor_set(v___x_2587_, 2, v___x_2600_);
lean_ctor_set(v___x_2587_, 1, v___x_2597_);
lean_ctor_set(v___x_2587_, 0, v___x_2596_);
v___x_2602_ = v___x_2587_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2628_, 2, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 3, v___x_2602_);
lean_ctor_set(v___x_2574_, 2, v___x_2595_);
lean_ctor_set(v___x_2574_, 1, v_binderName_2594_);
lean_ctor_set(v___x_2574_, 0, v_fvarId_2593_);
v___x_2604_ = v___x_2574_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_fvarId_2593_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_binderName_2594_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v_lctx_2606_; lean_object* v_nextIdx_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2626_; 
v___x_2605_ = lean_st_ref_take(v_a_2567_);
v_lctx_2606_ = lean_ctor_get(v___x_2605_, 0);
v_nextIdx_2607_ = lean_ctor_get(v___x_2605_, 1);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2609_ = v___x_2605_;
v_isShared_2610_ = v_isSharedCheck_2626_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_nextIdx_2607_);
lean_inc(v_lctx_2606_);
lean_dec(v___x_2605_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2626_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_inc_ref(v___x_2604_);
v___x_2611_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2589_, v_lctx_2606_, v___x_2604_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2625_, 1, v_nextIdx_2607_);
v___x_2613_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = lean_st_ref_put(v_a_2567_, v___x_2613_);
v___x_2615_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2585_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2624_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2604_);
lean_ctor_set(v___x_2620_, 1, v_a_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_dec_ref(v___x_2604_);
return v___x_2615_;
}
}
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_del_object(v___x_2587_);
lean_dec_ref(v_code_2585_);
lean_dec_ref(v_params_2584_);
lean_del_object(v___x_2574_);
lean_dec(v_discr_2571_);
v_a_2629_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2591_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2591_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_dec(v___x_2583_);
lean_del_object(v___x_2574_);
lean_dec(v_discr_2571_);
v___x_2639_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_2640_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2639_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
return v___x_2640_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2645_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = lean_unsigned_to_nat(192u);
v___x_2648_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2649_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2650_ = l_mkPanicMessageWithDecl(v___x_2649_, v___x_2648_, v___x_2647_, v___x_2646_, v___x_2645_);
return v___x_2650_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2652_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2653_ = lean_unsigned_to_nat(34u);
v___x_2654_ = lean_unsigned_to_nat(193u);
v___x_2655_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2656_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2657_ = l_mkPanicMessageWithDecl(v___x_2656_, v___x_2655_, v___x_2654_, v___x_2653_, v___x_2652_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_2658_, lean_object* v_uintName_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_discr_2666_; lean_object* v_alts_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2737_; 
v_discr_2666_ = lean_ctor_get(v_c_2658_, 2);
v_alts_2667_ = lean_ctor_get(v_c_2658_, 3);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_c_2658_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; 
v_unused_2738_ = lean_ctor_get(v_c_2658_, 1);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_c_2658_, 0);
lean_dec(v_unused_2739_);
v___x_2669_ = v_c_2658_;
v_isShared_2670_ = v_isSharedCheck_2737_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_alts_2667_);
lean_inc(v_discr_2666_);
lean_dec(v_c_2658_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2737_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; 
v___x_2671_ = lean_array_get_size(v_alts_2667_);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_dec_eq(v___x_2671_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_del_object(v___x_2669_);
lean_dec_ref(v_alts_2667_);
lean_dec(v_discr_2666_);
lean_dec(v_uintName_2659_);
v___x_2674_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_2675_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2674_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2677_ = lean_unsigned_to_nat(0u);
v___x_2678_ = lean_array_get(v___x_2676_, v_alts_2667_, v___x_2677_);
lean_dec_ref(v_alts_2667_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_params_2679_; lean_object* v_code_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2733_; 
v_params_2679_ = lean_ctor_get(v___x_2678_, 1);
v_code_2680_ = lean_ctor_get(v___x_2678_, 2);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2734_);
v___x_2682_ = v___x_2678_;
v_isShared_2683_ = v_isSharedCheck_2733_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_code_2680_);
lean_inc(v_params_2679_);
lean_dec(v___x_2678_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2733_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
uint8_t v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2684_ = 0;
v___x_2685_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2686_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2684_, v_params_2679_, v_a_2662_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2687_; lean_object* v_fvarId_2688_; lean_object* v_binderName_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
lean_dec_ref_known(v___x_2686_, 1);
v___x_2687_ = lean_array_get(v___x_2685_, v_params_2679_, v___x_2677_);
lean_dec_ref(v_params_2679_);
v_fvarId_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_fvarId_2688_);
v_binderName_2689_ = lean_ctor_get(v___x_2687_, 1);
lean_inc(v_binderName_2689_);
lean_dec(v___x_2687_);
v___x_2690_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2691_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4));
v___x_2692_ = l_Lean_Name_str___override(v_uintName_2659_, v___x_2691_);
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_discr_2666_);
v___x_2695_ = lean_mk_empty_array_with_capacity(v___x_2672_);
v___x_2696_ = lean_array_push(v___x_2695_, v___x_2694_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set_tag(v___x_2682_, 3);
lean_ctor_set(v___x_2682_, 2, v___x_2696_);
lean_ctor_set(v___x_2682_, 1, v___x_2693_);
lean_ctor_set(v___x_2682_, 0, v___x_2692_);
v___x_2698_ = v___x_2682_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2692_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 3, v___x_2698_);
lean_ctor_set(v___x_2669_, 2, v___x_2690_);
lean_ctor_set(v___x_2669_, 1, v_binderName_2689_);
lean_ctor_set(v___x_2669_, 0, v_fvarId_2688_);
v___x_2700_ = v___x_2669_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_fvarId_2688_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_binderName_2689_);
lean_ctor_set(v_reuseFailAlloc_2723_, 2, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2723_, 3, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v_lctx_2702_; lean_object* v_nextIdx_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2722_; 
v___x_2701_ = lean_st_ref_take(v_a_2662_);
v_lctx_2702_ = lean_ctor_get(v___x_2701_, 0);
v_nextIdx_2703_ = lean_ctor_get(v___x_2701_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2722_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_nextIdx_2703_);
lean_inc(v_lctx_2702_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2722_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
lean_inc_ref(v___x_2700_);
v___x_2707_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2684_, v_lctx_2702_, v___x_2700_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2707_);
v___x_2709_ = v___x_2705_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_nextIdx_2703_);
v___x_2709_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = lean_st_ref_put(v_a_2662_, v___x_2709_);
v___x_2711_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2680_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2720_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2720_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2720_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2700_);
lean_ctor_set(v___x_2716_, 1, v_a_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2716_);
v___x_2718_ = v___x_2714_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
else
{
lean_dec_ref(v___x_2700_);
return v___x_2711_;
}
}
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_del_object(v___x_2682_);
lean_dec_ref(v_code_2680_);
lean_dec_ref(v_params_2679_);
lean_del_object(v___x_2669_);
lean_dec(v_discr_2666_);
lean_dec(v_uintName_2659_);
v_a_2725_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2686_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2686_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_dec(v___x_2678_);
lean_del_object(v___x_2669_);
lean_dec(v_discr_2666_);
lean_dec(v_uintName_2659_);
v___x_2735_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5);
v___x_2736_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2735_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2736_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2740_ = lean_box(0);
v___x_2741_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_2742_ = l_Lean_mkConst(v___x_2741_, v___x_2740_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = lean_box(0);
v___x_2750_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_2751_ = l_Lean_mkConst(v___x_2750_, v___x_2749_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_2764_ = l_Lean_mkConst(v___x_2763_, v___x_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_2797_, size_t v_sz_2798_, size_t v_i_2799_, lean_object* v_bs_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_lt(v_i_2799_, v_sz_2798_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
lean_dec(v___x_2797_);
v___x_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2808_, 0, v_bs_2800_);
return v___x_2808_;
}
else
{
lean_object* v_v_2809_; lean_object* v___x_2810_; lean_object* v_bs_x27_2811_; lean_object* v_a_2813_; 
v_v_2809_ = lean_array_uget(v_bs_2800_, v_i_2799_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v_bs_x27_2811_ = lean_array_uset(v_bs_2800_, v_i_2799_, v___x_2810_);
if (lean_obj_tag(v_v_2809_) == 0)
{
lean_object* v_ctorName_2818_; lean_object* v_params_2819_; lean_object* v_code_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2947_; 
v_ctorName_2818_ = lean_ctor_get(v_v_2809_, 0);
v_params_2819_ = lean_ctor_get(v_v_2809_, 1);
v_code_2820_ = lean_ctor_get(v_v_2809_, 2);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_v_2809_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2822_ = v_v_2809_;
v_isShared_2823_ = v_isSharedCheck_2947_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_code_2820_);
lean_inc(v_params_2819_);
lean_inc(v_ctorName_2818_);
lean_dec(v_v_2809_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2947_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2824_ = 0;
v___x_2825_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2826_ = lean_box(0);
v___x_2827_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2828_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2824_, v_params_2819_, v___y_2803_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
lean_dec_ref_known(v___x_2828_, 1);
v___x_2829_ = lean_array_get(v___x_2825_, v_params_2819_, v___x_2810_);
lean_dec_ref(v_params_2819_);
v___x_2830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_2831_ = lean_name_eq(v_ctorName_2818_, v___x_2830_);
lean_dec(v_ctorName_2818_);
if (v___x_2831_ == 0)
{
lean_object* v_fvarId_2832_; lean_object* v_binderName_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_lctx_2841_; lean_object* v_nextIdx_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2867_; 
v_fvarId_2832_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_fvarId_2832_);
v_binderName_2833_ = lean_ctor_get(v___x_2829_, 1);
lean_inc(v_binderName_2833_);
lean_dec(v___x_2829_);
v___x_2834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = lean_mk_empty_array_with_capacity(v___x_2835_);
lean_inc(v___x_2797_);
v___x_2837_ = lean_array_push(v___x_2836_, v___x_2797_);
v___x_2838_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2834_);
lean_ctor_set(v___x_2838_, 1, v___x_2826_);
lean_ctor_set(v___x_2838_, 2, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2839_, 0, v_fvarId_2832_);
lean_ctor_set(v___x_2839_, 1, v_binderName_2833_);
lean_ctor_set(v___x_2839_, 2, v___x_2827_);
lean_ctor_set(v___x_2839_, 3, v___x_2838_);
v___x_2840_ = lean_st_ref_take(v___y_2803_);
v_lctx_2841_ = lean_ctor_get(v___x_2840_, 0);
v_nextIdx_2842_ = lean_ctor_get(v___x_2840_, 1);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2844_ = v___x_2840_;
v_isShared_2845_ = v_isSharedCheck_2867_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_nextIdx_2842_);
lean_inc(v_lctx_2841_);
lean_dec(v___x_2840_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2867_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_inc_ref(v___x_2839_);
v___x_2846_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2824_, v_lctx_2841_, v___x_2839_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2846_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2846_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v_nextIdx_2842_);
v___x_2848_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_st_ref_put(v___y_2803_, v___x_2848_);
v___x_2850_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2820_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_2853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2839_);
lean_ctor_set(v___x_2854_, 1, v_a_2851_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 2, v___x_2854_);
lean_ctor_set(v___x_2822_, 1, v___x_2853_);
lean_ctor_set(v___x_2822_, 0, v___x_2852_);
v___x_2856_ = v___x_2822_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v_a_2813_ = v___x_2856_;
goto v___jp_2812_;
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref_known(v___x_2839_, 4);
lean_del_object(v___x_2822_);
lean_dec_ref(v_bs_x27_2811_);
lean_dec(v___x_2797_);
v_a_2858_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2850_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2850_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_2869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_mk_empty_array_with_capacity(v___x_2870_);
lean_inc(v___x_2797_);
v___x_2872_ = lean_array_push(v___x_2871_, v___x_2797_);
v___x_2873_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2869_);
lean_ctor_set(v___x_2873_, 1, v___x_2826_);
lean_ctor_set(v___x_2873_, 2, v___x_2872_);
v___x_2874_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2824_, v___x_2868_, v___x_2827_, v___x_2873_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_2877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_2878_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2824_, v___x_2876_, v___x_2827_, v___x_2877_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_fvarId_2880_; lean_object* v_binderName_2881_; lean_object* v_fvarId_2882_; lean_object* v_fvarId_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v_lctx_2894_; lean_object* v_nextIdx_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2922_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v_fvarId_2880_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_fvarId_2880_);
v_binderName_2881_ = lean_ctor_get(v___x_2829_, 1);
lean_inc(v_binderName_2881_);
lean_dec(v___x_2829_);
v_fvarId_2882_ = lean_ctor_get(v_a_2875_, 0);
v_fvarId_2883_ = lean_ctor_get(v_a_2879_, 0);
v___x_2884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_2882_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v_fvarId_2882_);
lean_inc(v_fvarId_2883_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_fvarId_2883_);
v___x_2887_ = lean_unsigned_to_nat(2u);
v___x_2888_ = lean_mk_empty_array_with_capacity(v___x_2887_);
v___x_2889_ = lean_array_push(v___x_2888_, v___x_2885_);
v___x_2890_ = lean_array_push(v___x_2889_, v___x_2886_);
v___x_2891_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2884_);
lean_ctor_set(v___x_2891_, 1, v___x_2826_);
lean_ctor_set(v___x_2891_, 2, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2892_, 0, v_fvarId_2880_);
lean_ctor_set(v___x_2892_, 1, v_binderName_2881_);
lean_ctor_set(v___x_2892_, 2, v___x_2827_);
lean_ctor_set(v___x_2892_, 3, v___x_2891_);
v___x_2893_ = lean_st_ref_take(v___y_2803_);
v_lctx_2894_ = lean_ctor_get(v___x_2893_, 0);
v_nextIdx_2895_ = lean_ctor_get(v___x_2893_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2897_ = v___x_2893_;
v_isShared_2898_ = v_isSharedCheck_2922_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_nextIdx_2895_);
lean_inc(v_lctx_2894_);
lean_dec(v___x_2893_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2922_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
lean_inc_ref(v___x_2892_);
v___x_2899_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2824_, v_lctx_2894_, v___x_2892_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2899_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_nextIdx_2895_);
v___x_2901_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = lean_st_ref_put(v___y_2803_, v___x_2901_);
v___x_2903_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2820_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_2906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2892_);
lean_ctor_set(v___x_2907_, 1, v_a_2904_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2879_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_a_2875_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 2, v___x_2909_);
lean_ctor_set(v___x_2822_, 1, v___x_2906_);
lean_ctor_set(v___x_2822_, 0, v___x_2905_);
v___x_2911_ = v___x_2822_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
v_a_2813_ = v___x_2911_;
goto v___jp_2812_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref_known(v___x_2892_, 4);
lean_dec(v_a_2879_);
lean_dec(v_a_2875_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_bs_x27_2811_);
lean_dec(v___x_2797_);
v_a_2913_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2903_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2903_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_a_2875_);
lean_dec(v___x_2829_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_code_2820_);
lean_dec_ref(v_bs_x27_2811_);
lean_dec(v___x_2797_);
v_a_2923_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2878_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2878_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v___x_2829_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_code_2820_);
lean_dec_ref(v_bs_x27_2811_);
lean_dec(v___x_2797_);
v_a_2931_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2874_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2874_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_del_object(v___x_2822_);
lean_dec_ref(v_code_2820_);
lean_dec_ref(v_params_2819_);
lean_dec(v_ctorName_2818_);
lean_dec_ref(v_bs_x27_2811_);
lean_dec(v___x_2797_);
v_a_2939_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2828_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2828_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
else
{
lean_object* v_code_2948_; lean_object* v___x_2949_; 
v_code_2948_ = lean_ctor_get(v_v_2809_, 0);
lean_inc_ref(v_code_2948_);
v___x_2949_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2948_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2809_, v_a_2950_);
v_a_2813_ = v___x_2951_;
goto v___jp_2812_;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec_ref_known(v_v_2809_, 1);
lean_dec_ref(v_bs_x27_2811_);
lean_dec(v___x_2797_);
v_a_2952_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2949_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2949_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2812_:
{
size_t v___x_2814_; size_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2799_, v___x_2814_);
v___x_2816_ = lean_array_uset(v_bs_x27_2811_, v_i_2799_, v_a_2813_);
v_i_2799_ = v___x_2815_;
v_bs_2800_ = v___x_2816_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_resultType_2967_; lean_object* v_discr_2968_; lean_object* v_alts_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3066_; 
v_resultType_2967_ = lean_ctor_get(v_c_2960_, 1);
v_discr_2968_ = lean_ctor_get(v_c_2960_, 2);
v_alts_2969_ = lean_ctor_get(v_c_2960_, 3);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_c_2960_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; 
v_unused_3067_ = lean_ctor_get(v_c_2960_, 0);
lean_dec(v_unused_3067_);
v___x_2971_ = v_c_2960_;
v_isShared_2972_ = v_isSharedCheck_3066_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_alts_2969_);
lean_inc(v_discr_2968_);
lean_inc(v_resultType_2967_);
lean_dec(v_c_2960_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3066_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
uint8_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = 0;
v___x_2974_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_2967_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2978_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_2979_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_2980_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2973_, v___x_2978_, v___x_2977_, v___x_2979_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_fvarId_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v_fvarId_2982_ = lean_ctor_get(v_a_2981_, 0);
v___x_2983_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_2984_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_2985_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_2982_);
v___x_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_fvarId_2982_);
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_mk_empty_array_with_capacity(v___x_2987_);
v___x_2989_ = lean_array_push(v___x_2988_, v___x_2986_);
v___x_2990_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2985_);
lean_ctor_set(v___x_2990_, 1, v___x_2976_);
lean_ctor_set(v___x_2990_, 2, v___x_2989_);
v___x_2991_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2973_, v___x_2983_, v___x_2984_, v___x_2990_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v_fvarId_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v_fvarId_2993_ = lean_ctor_get(v_a_2992_, 0);
v___x_2994_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_2995_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_2996_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_2997_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v_discr_2968_);
lean_inc(v_fvarId_2993_);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_fvarId_2993_);
v___x_3000_ = lean_unsigned_to_nat(2u);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_3000_);
lean_inc_ref(v___x_2998_);
v___x_3002_ = lean_array_push(v___x_3001_, v___x_2998_);
v___x_3003_ = lean_array_push(v___x_3002_, v___x_2999_);
v___x_3004_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3004_, 0, v___x_2997_);
lean_ctor_set(v___x_3004_, 1, v___x_2976_);
lean_ctor_set(v___x_3004_, 2, v___x_3003_);
v___x_3005_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2973_, v___x_2994_, v___x_2996_, v___x_3004_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; size_t v_sz_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v_sz_3007_ = lean_array_size(v_alts_2969_);
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_2998_, v_sz_3007_, v___x_3008_, v_alts_2969_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3025_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3025_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3025_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v_fvarId_3014_; lean_object* v___x_3016_; 
v_fvarId_3014_ = lean_ctor_get(v_a_3006_, 0);
lean_inc(v_fvarId_3014_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 3, v_a_3010_);
lean_ctor_set(v___x_2971_, 2, v_fvarId_3014_);
lean_ctor_set(v___x_2971_, 1, v_a_2975_);
lean_ctor_set(v___x_2971_, 0, v___x_2995_);
v___x_3016_ = v___x_2971_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_a_2975_);
lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_fvarId_3014_);
lean_ctor_set(v_reuseFailAlloc_3024_, 3, v_a_3010_);
v___x_3016_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3017_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v_a_3006_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_a_2992_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v_a_2981_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3020_);
v___x_3022_ = v___x_3012_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec(v_a_3006_);
lean_dec(v_a_2992_);
lean_dec(v_a_2981_);
lean_dec(v_a_2975_);
lean_del_object(v___x_2971_);
v_a_3026_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3009_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3009_);
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
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref_known(v___x_2998_, 1);
lean_dec(v_a_2992_);
lean_dec(v_a_2981_);
lean_dec(v_a_2975_);
lean_del_object(v___x_2971_);
lean_dec_ref(v_alts_2969_);
v_a_3034_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3005_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3005_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v_a_2981_);
lean_dec(v_a_2975_);
lean_del_object(v___x_2971_);
lean_dec_ref(v_alts_2969_);
lean_dec(v_discr_2968_);
v_a_3042_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_2991_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_2991_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_2975_);
lean_del_object(v___x_2971_);
lean_dec_ref(v_alts_2969_);
lean_dec(v_discr_2968_);
v_a_3050_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_2980_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_2980_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_2971_);
lean_dec_ref(v_alts_2969_);
lean_dec(v_discr_2968_);
v_a_3058_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2974_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2974_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3077_, size_t v_sz_3078_, size_t v_i_3079_, lean_object* v_bs_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v___x_3087_; 
v___x_3087_ = lean_usize_dec_lt(v_i_3079_, v_sz_3078_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; 
lean_dec(v___x_3077_);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v_bs_3080_);
return v___x_3088_;
}
else
{
lean_object* v_v_3089_; lean_object* v___x_3090_; lean_object* v_bs_x27_3091_; lean_object* v_a_3093_; 
v_v_3089_ = lean_array_uget(v_bs_3080_, v_i_3079_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v_bs_x27_3091_ = lean_array_uset(v_bs_3080_, v_i_3079_, v___x_3090_);
if (lean_obj_tag(v_v_3089_) == 0)
{
lean_object* v_ctorName_3098_; lean_object* v_params_3099_; lean_object* v_code_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3187_; 
v_ctorName_3098_ = lean_ctor_get(v_v_3089_, 0);
v_params_3099_ = lean_ctor_get(v_v_3089_, 1);
v_code_3100_ = lean_ctor_get(v_v_3089_, 2);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_v_3089_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3102_ = v_v_3089_;
v_isShared_3103_ = v_isSharedCheck_3187_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_code_3100_);
lean_inc(v_params_3099_);
lean_inc(v_ctorName_3098_);
lean_dec(v_v_3089_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3187_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3104_ = 0;
v___x_3105_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_3106_ = lean_box(0);
v___x_3107_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3108_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3104_, v_params_3099_, v___y_3083_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3109_; uint8_t v___x_3110_; 
lean_dec_ref_known(v___x_3108_, 1);
v___x_3109_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_3110_ = lean_name_eq(v_ctorName_3098_, v___x_3109_);
lean_dec(v_ctorName_3098_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; 
lean_dec_ref(v_params_3099_);
v___x_3111_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3100_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 2, v_a_3112_);
lean_ctor_set(v___x_3102_, 1, v___x_3114_);
lean_ctor_set(v___x_3102_, 0, v___x_3113_);
v___x_3116_ = v___x_3102_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_a_3112_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
v_a_3093_ = v___x_3116_;
goto v___jp_3092_;
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_del_object(v___x_3102_);
lean_dec_ref(v_bs_x27_3091_);
lean_dec(v___x_3077_);
v_a_3118_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3111_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3111_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3126_ = lean_array_get(v___x_3105_, v_params_3099_, v___x_3090_);
lean_dec_ref(v_params_3099_);
v___x_3127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_3128_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3129_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3104_, v___x_3127_, v___x_3107_, v___x_3128_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v_fvarId_3131_; lean_object* v_binderName_3132_; lean_object* v_fvarId_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v_lctx_3143_; lean_object* v_nextIdx_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3170_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v___x_3129_, 1);
v_fvarId_3131_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_fvarId_3131_);
v_binderName_3132_ = lean_ctor_get(v___x_3126_, 1);
lean_inc(v_binderName_3132_);
lean_dec(v___x_3126_);
v_fvarId_3133_ = lean_ctor_get(v_a_3130_, 0);
v___x_3134_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_3133_);
v___x_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_fvarId_3133_);
v___x_3136_ = lean_unsigned_to_nat(2u);
v___x_3137_ = lean_mk_empty_array_with_capacity(v___x_3136_);
lean_inc(v___x_3077_);
v___x_3138_ = lean_array_push(v___x_3137_, v___x_3077_);
v___x_3139_ = lean_array_push(v___x_3138_, v___x_3135_);
v___x_3140_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3134_);
lean_ctor_set(v___x_3140_, 1, v___x_3106_);
lean_ctor_set(v___x_3140_, 2, v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3141_, 0, v_fvarId_3131_);
lean_ctor_set(v___x_3141_, 1, v_binderName_3132_);
lean_ctor_set(v___x_3141_, 2, v___x_3107_);
lean_ctor_set(v___x_3141_, 3, v___x_3140_);
v___x_3142_ = lean_st_ref_take(v___y_3083_);
v_lctx_3143_ = lean_ctor_get(v___x_3142_, 0);
v_nextIdx_3144_ = lean_ctor_get(v___x_3142_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3146_ = v___x_3142_;
v_isShared_3147_ = v_isSharedCheck_3170_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_nextIdx_3144_);
lean_inc(v_lctx_3143_);
lean_dec(v___x_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3170_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3150_; 
lean_inc_ref(v___x_3141_);
v___x_3148_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3104_, v_lctx_3143_, v___x_3141_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3148_);
v___x_3150_ = v___x_3146_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_nextIdx_3144_);
v___x_3150_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_st_ref_put(v___y_3083_, v___x_3150_);
v___x_3152_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3100_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_3155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3141_);
lean_ctor_set(v___x_3156_, 1, v_a_3153_);
v___x_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3157_, 0, v_a_3130_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 2, v___x_3157_);
lean_ctor_set(v___x_3102_, 1, v___x_3155_);
lean_ctor_set(v___x_3102_, 0, v___x_3154_);
v___x_3159_ = v___x_3102_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v___x_3157_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
v_a_3093_ = v___x_3159_;
goto v___jp_3092_;
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec_ref_known(v___x_3141_, 4);
lean_dec(v_a_3130_);
lean_del_object(v___x_3102_);
lean_dec_ref(v_bs_x27_3091_);
lean_dec(v___x_3077_);
v_a_3161_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3152_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3152_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v___x_3126_);
lean_del_object(v___x_3102_);
lean_dec_ref(v_code_3100_);
lean_dec_ref(v_bs_x27_3091_);
lean_dec(v___x_3077_);
v_a_3171_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3129_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3129_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_del_object(v___x_3102_);
lean_dec_ref(v_code_3100_);
lean_dec_ref(v_params_3099_);
lean_dec(v_ctorName_3098_);
lean_dec_ref(v_bs_x27_3091_);
lean_dec(v___x_3077_);
v_a_3179_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3108_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3108_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
}
else
{
lean_object* v_code_3188_; lean_object* v___x_3189_; 
v_code_3188_ = lean_ctor_get(v_v_3089_, 0);
lean_inc_ref(v_code_3188_);
v___x_3189_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3188_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3191_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3189_, 1);
v___x_3191_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3089_, v_a_3190_);
v_a_3093_ = v___x_3191_;
goto v___jp_3092_;
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref_known(v_v_3089_, 1);
lean_dec_ref(v_bs_x27_3091_);
lean_dec(v___x_3077_);
v_a_3192_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3189_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3189_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
v___jp_3092_:
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = ((size_t)1ULL);
v___x_3095_ = lean_usize_add(v_i_3079_, v___x_3094_);
v___x_3096_ = lean_array_uset(v_bs_x27_3091_, v_i_3079_, v_a_3093_);
v_i_3079_ = v___x_3095_;
v_bs_3080_ = v___x_3096_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_resultType_3207_; lean_object* v_discr_3208_; lean_object* v_alts_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3286_; 
v_resultType_3207_ = lean_ctor_get(v_c_3200_, 1);
v_discr_3208_ = lean_ctor_get(v_c_3200_, 2);
v_alts_3209_ = lean_ctor_get(v_c_3200_, 3);
v_isSharedCheck_3286_ = !lean_is_exclusive(v_c_3200_);
if (v_isSharedCheck_3286_ == 0)
{
lean_object* v_unused_3287_; 
v_unused_3287_ = lean_ctor_get(v_c_3200_, 0);
lean_dec(v_unused_3287_);
v___x_3211_ = v_c_3200_;
v_isShared_3212_ = v_isSharedCheck_3286_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_alts_3209_);
lean_inc(v_discr_3208_);
lean_inc(v_resultType_3207_);
lean_dec(v_c_3200_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3286_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
uint8_t v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = 0;
v___x_3214_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3207_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3216_ = lean_box(0);
v___x_3217_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3218_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3219_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_3220_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3213_, v___x_3218_, v___x_3217_, v___x_3219_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v_fvarId_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v_fvarId_3222_ = lean_ctor_get(v_a_3221_, 0);
v___x_3223_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3224_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3225_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3226_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9));
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_discr_3208_);
lean_inc(v_fvarId_3222_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_fvarId_3222_);
v___x_3229_ = lean_unsigned_to_nat(2u);
v___x_3230_ = lean_mk_empty_array_with_capacity(v___x_3229_);
lean_inc_ref(v___x_3227_);
v___x_3231_ = lean_array_push(v___x_3230_, v___x_3227_);
v___x_3232_ = lean_array_push(v___x_3231_, v___x_3228_);
v___x_3233_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3226_);
lean_ctor_set(v___x_3233_, 1, v___x_3216_);
lean_ctor_set(v___x_3233_, 2, v___x_3232_);
v___x_3234_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3213_, v___x_3223_, v___x_3225_, v___x_3233_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; size_t v_sz_3236_; size_t v___x_3237_; lean_object* v___x_3238_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v_sz_3236_ = lean_array_size(v_alts_3209_);
v___x_3237_ = ((size_t)0ULL);
v___x_3238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3227_, v_sz_3236_, v___x_3237_, v_alts_3209_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3253_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3253_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3253_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v_fvarId_3243_; lean_object* v___x_3245_; 
v_fvarId_3243_ = lean_ctor_get(v_a_3235_, 0);
lean_inc(v_fvarId_3243_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 3, v_a_3239_);
lean_ctor_set(v___x_3211_, 2, v_fvarId_3243_);
lean_ctor_set(v___x_3211_, 1, v_a_3215_);
lean_ctor_set(v___x_3211_, 0, v___x_3224_);
v___x_3245_ = v___x_3211_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_a_3215_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_fvarId_3243_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_a_3239_);
v___x_3245_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3246_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3247_, 0, v_a_3235_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_a_3221_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3248_);
v___x_3250_ = v___x_3241_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec(v_a_3235_);
lean_dec(v_a_3221_);
lean_dec(v_a_3215_);
lean_del_object(v___x_3211_);
v_a_3254_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3238_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3238_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref_known(v___x_3227_, 1);
lean_dec(v_a_3221_);
lean_dec(v_a_3215_);
lean_del_object(v___x_3211_);
lean_dec_ref(v_alts_3209_);
v_a_3262_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3234_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3234_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec(v_a_3215_);
lean_del_object(v___x_3211_);
lean_dec_ref(v_alts_3209_);
lean_dec(v_discr_3208_);
v_a_3270_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3220_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3220_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_del_object(v___x_3211_);
lean_dec_ref(v_alts_3209_);
lean_dec(v_discr_3208_);
v_a_3278_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_3214_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3214_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v_decl_3304_; lean_object* v_k_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; 
switch(lean_obj_tag(v_code_3288_))
{
case 0:
{
lean_object* v_decl_3412_; lean_object* v_k_3413_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v_value_3469_; 
v_decl_3412_ = lean_ctor_get(v_code_3288_, 0);
v_k_3413_ = lean_ctor_get(v_code_3288_, 1);
v_value_3469_ = lean_ctor_get(v_decl_3412_, 3);
lean_inc(v_value_3469_);
if (lean_obj_tag(v_value_3469_) == 3)
{
lean_object* v_declName_3470_; 
v_declName_3470_ = lean_ctor_get(v_value_3469_, 0);
lean_inc(v_declName_3470_);
if (lean_obj_tag(v_declName_3470_) == 1)
{
lean_object* v_pre_3471_; 
v_pre_3471_ = lean_ctor_get(v_declName_3470_, 0);
lean_inc(v_pre_3471_);
if (lean_obj_tag(v_pre_3471_) == 1)
{
lean_object* v_pre_3472_; 
v_pre_3472_ = lean_ctor_get(v_pre_3471_, 0);
if (lean_obj_tag(v_pre_3472_) == 0)
{
lean_object* v_type_3473_; lean_object* v_args_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3544_; 
v_type_3473_ = lean_ctor_get(v_decl_3412_, 2);
v_args_3474_ = lean_ctor_get(v_value_3469_, 2);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_value_3469_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; lean_object* v_unused_3546_; 
v_unused_3545_ = lean_ctor_get(v_value_3469_, 1);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_value_3469_, 0);
lean_dec(v_unused_3546_);
v___x_3476_ = v_value_3469_;
v_isShared_3477_ = v_isSharedCheck_3544_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_args_3474_);
lean_dec(v_value_3469_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3544_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v_str_3478_; lean_object* v_str_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v_str_3478_ = lean_ctor_get(v_declName_3470_, 1);
lean_inc_ref(v_str_3478_);
lean_dec_ref_known(v_declName_3470_, 2);
v_str_3479_ = lean_ctor_get(v_pre_3471_, 1);
lean_inc_ref(v_str_3479_);
lean_dec_ref_known(v_pre_3471_, 2);
v___x_3480_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__5));
v___x_3481_ = lean_string_dec_eq(v_str_3479_, v___x_3480_);
lean_dec_ref(v_str_3479_);
if (v___x_3481_ == 0)
{
lean_dec_ref(v_str_3478_);
lean_del_object(v___x_3476_);
lean_dec_ref(v_args_3474_);
v___y_3415_ = v_a_3289_;
v___y_3416_ = v_a_3290_;
v___y_3417_ = v_a_3291_;
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3482_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_3483_ = lean_string_dec_eq(v_str_3478_, v___x_3482_);
lean_dec_ref(v_str_3478_);
if (v___x_3483_ == 0)
{
lean_del_object(v___x_3476_);
lean_dec_ref(v_args_3474_);
v___y_3415_ = v_a_3289_;
v___y_3416_ = v_a_3290_;
v___y_3417_ = v_a_3291_;
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
goto v___jp_3414_;
}
else
{
lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3541_; 
lean_inc_ref(v_type_3473_);
lean_inc_ref(v_k_3413_);
lean_inc_ref(v_decl_3412_);
v_isSharedCheck_3541_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3541_ == 0)
{
lean_object* v_unused_3542_; lean_object* v_unused_3543_; 
v_unused_3542_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3543_);
v___x_3485_ = v_code_3288_;
v_isShared_3486_ = v_isSharedCheck_3541_;
goto v_resetjp_3484_;
}
else
{
lean_dec(v_code_3288_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3541_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3487_ = lean_array_get_size(v_args_3474_);
v___x_3488_ = lean_unsigned_to_nat(1u);
v___x_3489_ = lean_nat_dec_eq(v___x_3487_, v___x_3488_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
lean_del_object(v___x_3485_);
lean_del_object(v___x_3476_);
lean_dec_ref(v_args_3474_);
lean_dec_ref(v_type_3473_);
lean_dec_ref(v_k_3413_);
lean_dec_ref(v_decl_3412_);
v___x_3490_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3491_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3490_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3491_;
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3492_ = lean_unsigned_to_nat(0u);
v___x_3493_ = lean_array_fget(v_args_3474_, v___x_3492_);
lean_dec_ref(v_args_3474_);
v___x_3494_ = 0;
v___x_3495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3496_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_3497_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3494_, v___x_3495_, v___x_3496_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v_fvarId_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v_fvarId_3499_ = lean_ctor_get(v_a_3498_, 0);
v___x_3500_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3501_ = lean_box(0);
lean_inc(v_fvarId_3499_);
v___x_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_fvarId_3499_);
v___x_3503_ = lean_unsigned_to_nat(2u);
v___x_3504_ = lean_mk_empty_array_with_capacity(v___x_3503_);
v___x_3505_ = lean_array_push(v___x_3504_, v___x_3493_);
v___x_3506_ = lean_array_push(v___x_3505_, v___x_3502_);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 2, v___x_3506_);
lean_ctor_set(v___x_3476_, 1, v___x_3501_);
lean_ctor_set(v___x_3476_, 0, v___x_3500_);
v___x_3508_ = v___x_3476_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3532_, 2, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3509_; 
v___x_3509_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3494_, v_decl_3412_, v_type_3473_, v___x_3508_, v_a_3291_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3413_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3523_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3523_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3523_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 1, v_a_3512_);
lean_ctor_set(v___x_3485_, 0, v_a_3510_);
v___x_3517_ = v___x_3485_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3510_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3518_, 0, v_a_3498_);
lean_ctor_set(v___x_3518_, 1, v___x_3517_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3518_);
v___x_3520_ = v___x_3514_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
else
{
lean_dec(v_a_3510_);
lean_dec(v_a_3498_);
lean_del_object(v___x_3485_);
return v___x_3511_;
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec(v_a_3498_);
lean_del_object(v___x_3485_);
lean_dec_ref(v_k_3413_);
v_a_3524_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3509_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3509_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v___x_3493_);
lean_del_object(v___x_3485_);
lean_del_object(v___x_3476_);
lean_dec_ref(v_type_3473_);
lean_dec_ref(v_k_3413_);
lean_dec_ref(v_decl_3412_);
v_a_3533_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3497_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3497_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
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
lean_dec_ref_known(v_pre_3471_, 2);
lean_dec_ref_known(v_declName_3470_, 2);
lean_dec_ref_known(v_value_3469_, 3);
v___y_3415_ = v_a_3289_;
v___y_3416_ = v_a_3290_;
v___y_3417_ = v_a_3291_;
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
goto v___jp_3414_;
}
}
else
{
lean_dec_ref_known(v_declName_3470_, 2);
lean_dec(v_pre_3471_);
lean_dec_ref_known(v_value_3469_, 3);
v___y_3415_ = v_a_3289_;
v___y_3416_ = v_a_3290_;
v___y_3417_ = v_a_3291_;
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
goto v___jp_3414_;
}
}
else
{
lean_dec(v_declName_3470_);
lean_dec_ref_known(v_value_3469_, 3);
v___y_3415_ = v_a_3289_;
v___y_3416_ = v_a_3290_;
v___y_3417_ = v_a_3291_;
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
goto v___jp_3414_;
}
}
else
{
lean_dec(v_value_3469_);
v___y_3415_ = v_a_3289_;
v___y_3416_ = v_a_3290_;
v___y_3417_ = v_a_3291_;
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
goto v___jp_3414_;
}
v___jp_3414_:
{
lean_object* v___x_3420_; 
lean_inc_ref(v_decl_3412_);
v___x_3420_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3412_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref_known(v___x_3420_, 1);
lean_inc_ref(v_k_3413_);
v___x_3422_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3413_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3460_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3460_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3460_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
size_t v___x_3427_; size_t v___x_3428_; uint8_t v___x_3429_; 
v___x_3427_ = lean_ptr_addr(v_k_3413_);
v___x_3428_ = lean_ptr_addr(v_a_3423_);
v___x_3429_ = lean_usize_dec_eq(v___x_3427_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3439_; 
v_isSharedCheck_3439_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; lean_object* v_unused_3441_; 
v_unused_3440_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3440_);
v_unused_3441_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3441_);
v___x_3431_ = v_code_3288_;
v_isShared_3432_ = v_isSharedCheck_3439_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v_code_3288_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3439_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v_a_3423_);
lean_ctor_set(v___x_3431_, 0, v_a_3421_);
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_a_3423_);
v___x_3434_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3436_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3434_);
v___x_3436_ = v___x_3425_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3434_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
size_t v___x_3442_; size_t v___x_3443_; uint8_t v___x_3444_; 
v___x_3442_ = lean_ptr_addr(v_decl_3412_);
v___x_3443_ = lean_ptr_addr(v_a_3421_);
v___x_3444_ = lean_usize_dec_eq(v___x_3442_, v___x_3443_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3454_; 
v_isSharedCheck_3454_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; lean_object* v_unused_3456_; 
v_unused_3455_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3455_);
v_unused_3456_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3456_);
v___x_3446_ = v_code_3288_;
v_isShared_3447_ = v_isSharedCheck_3454_;
goto v_resetjp_3445_;
}
else
{
lean_dec(v_code_3288_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3454_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v_a_3423_);
lean_ctor_set(v___x_3446_, 0, v_a_3421_);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3421_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_a_3423_);
v___x_3449_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3449_);
v___x_3451_ = v___x_3425_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
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
else
{
lean_object* v___x_3458_; 
lean_dec(v_a_3423_);
lean_dec(v_a_3421_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v_code_3288_);
v___x_3458_ = v___x_3425_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_code_3288_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
else
{
lean_dec(v_a_3421_);
lean_dec_ref_known(v_code_3288_, 2);
return v___x_3422_;
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref_known(v_code_3288_, 2);
v_a_3461_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3420_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3420_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_3547_; lean_object* v_args_3548_; size_t v_sz_3549_; size_t v___x_3550_; lean_object* v___x_3551_; 
v_fvarId_3547_ = lean_ctor_get(v_code_3288_, 0);
v_args_3548_ = lean_ctor_get(v_code_3288_, 1);
v_sz_3549_ = lean_array_size(v_args_3548_);
v___x_3550_ = ((size_t)0ULL);
lean_inc_ref(v_args_3548_);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3549_, v___x_3550_, v_args_3548_, v_a_3289_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3587_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3587_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3587_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
uint8_t v___x_3556_; 
v___x_3556_ = l_Lean_instBEqFVarId_beq(v_fvarId_3547_, v_fvarId_3547_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3566_; 
lean_inc(v_fvarId_3547_);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; lean_object* v_unused_3568_; 
v_unused_3567_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3567_);
v_unused_3568_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3568_);
v___x_3558_ = v_code_3288_;
v_isShared_3559_ = v_isSharedCheck_3566_;
goto v_resetjp_3557_;
}
else
{
lean_dec(v_code_3288_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3566_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v_a_3552_);
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_fvarId_3547_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_a_3552_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3563_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3561_);
v___x_3563_ = v___x_3554_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
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
else
{
size_t v___x_3569_; size_t v___x_3570_; uint8_t v___x_3571_; 
v___x_3569_ = lean_ptr_addr(v_args_3548_);
v___x_3570_ = lean_ptr_addr(v_a_3552_);
v___x_3571_ = lean_usize_dec_eq(v___x_3569_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3581_; 
lean_inc(v_fvarId_3547_);
v_isSharedCheck_3581_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; lean_object* v_unused_3583_; 
v_unused_3582_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3582_);
v_unused_3583_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3583_);
v___x_3573_ = v_code_3288_;
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v_code_3288_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 1, v_a_3552_);
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_fvarId_3547_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_a_3552_);
v___x_3576_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3576_);
v___x_3578_ = v___x_3554_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_object* v___x_3585_; 
lean_dec(v_a_3552_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v_code_3288_);
v___x_3585_ = v___x_3554_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_code_3288_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref_known(v_code_3288_, 2);
v_a_3588_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3551_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3551_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
case 4:
{
lean_object* v_cases_3596_; lean_object* v_typeName_3597_; lean_object* v_resultType_3598_; lean_object* v_discr_3599_; lean_object* v_alts_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v_cases_3596_ = lean_ctor_get(v_code_3288_, 0);
lean_inc_ref(v_cases_3596_);
v_typeName_3597_ = lean_ctor_get(v_cases_3596_, 0);
v_resultType_3598_ = lean_ctor_get(v_cases_3596_, 1);
v_discr_3599_ = lean_ctor_get(v_cases_3596_, 2);
v_alts_3600_ = lean_ctor_get(v_cases_3596_, 3);
v___x_3601_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3602_ = lean_name_eq(v_typeName_3597_, v___x_3601_);
if (v___x_3602_ == 0)
{
lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3604_ = lean_name_eq(v_typeName_3597_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; uint8_t v___x_3606_; 
v___x_3605_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__9));
v___x_3606_ = lean_name_eq(v_typeName_3597_, v___x_3605_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; uint8_t v___x_3608_; 
v___x_3607_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__11));
v___x_3608_ = lean_name_eq(v_typeName_3597_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3609_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__13));
v___x_3610_ = lean_name_eq(v_typeName_3597_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3611_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__15));
v___x_3612_ = lean_name_eq(v_typeName_3597_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3614_ = lean_name_eq(v_typeName_3597_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; uint8_t v___x_3616_; 
v___x_3615_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3616_ = lean_name_eq(v_typeName_3597_, v___x_3615_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3617_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3618_ = lean_name_eq(v_typeName_3597_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; uint8_t v___x_3620_; 
v___x_3619_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3620_ = lean_name_eq(v_typeName_3597_, v___x_3619_);
if (v___x_3620_ == 0)
{
lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3621_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3622_ = lean_name_eq(v_typeName_3597_, v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3623_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3624_ = lean_name_eq(v_typeName_3597_, v___x_3623_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3625_; uint8_t v___x_3626_; 
v___x_3625_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3626_ = lean_name_eq(v_typeName_3597_, v___x_3625_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3627_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3628_ = lean_name_eq(v_typeName_3597_, v___x_3627_);
if (v___x_3628_ == 0)
{
lean_object* v___x_3629_; 
lean_inc(v_typeName_3597_);
v___x_3629_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3597_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref_known(v___x_3629_, 1);
if (lean_obj_tag(v_a_3630_) == 1)
{
lean_object* v_val_3631_; lean_object* v___x_3632_; 
lean_dec_ref_known(v_code_3288_, 1);
v_val_3631_ = lean_ctor_get(v_a_3630_, 0);
lean_inc(v_val_3631_);
lean_dec_ref_known(v_a_3630_, 1);
v___x_3632_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3631_, v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec(v_val_3631_);
return v___x_3632_;
}
else
{
lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3731_; 
lean_inc_ref(v_alts_3600_);
lean_inc(v_discr_3599_);
lean_inc_ref(v_resultType_3598_);
lean_inc(v_typeName_3597_);
lean_dec(v_a_3630_);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_cases_3596_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; 
v_unused_3732_ = lean_ctor_get(v_cases_3596_, 3);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_cases_3596_, 2);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_cases_3596_, 1);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_cases_3596_, 0);
lean_dec(v_unused_3735_);
v___x_3634_ = v_cases_3596_;
v_isShared_3635_ = v_isSharedCheck_3731_;
goto v_resetjp_3633_;
}
else
{
lean_dec(v_cases_3596_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3731_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; 
lean_inc_ref(v_resultType_3598_);
v___x_3636_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3598_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3722_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3639_ = v___x_3636_;
v_isShared_3640_ = v_isSharedCheck_3722_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3636_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3722_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; lean_object* v_env_3642_; lean_object* v___x_3643_; 
v___x_3641_ = lean_st_ref_get(v_a_3293_);
v_env_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc_ref_n(v_env_3642_, 2);
lean_dec(v___x_3641_);
lean_inc(v_typeName_3597_);
v___x_3643_ = l_Lean_Environment_find_x3f(v_env_3642_, v_typeName_3597_, v___x_3628_);
if (lean_obj_tag(v___x_3643_) == 1)
{
lean_object* v_val_3644_; 
v_val_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_val_3644_);
lean_dec_ref_known(v___x_3643_, 1);
if (lean_obj_tag(v_val_3644_) == 5)
{
lean_object* v_val_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3721_; 
v_val_3645_ = lean_ctor_get(v_val_3644_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_val_3644_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3647_ = v_val_3644_;
v_isShared_3648_ = v_isSharedCheck_3721_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_val_3645_);
lean_dec(v_val_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3721_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v_toConstantVal_3649_; lean_object* v_name_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v_toConstantVal_3649_ = lean_ctor_get(v_val_3645_, 0);
lean_inc_ref(v_toConstantVal_3649_);
lean_dec_ref(v_val_3645_);
v_name_3650_ = lean_ctor_get(v_toConstantVal_3649_, 0);
lean_inc(v_name_3650_);
lean_dec_ref(v_toConstantVal_3649_);
v___x_3651_ = l_Lean_mkCasesOnName(v_name_3650_);
lean_inc_ref(v_env_3642_);
v___x_3652_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3642_, v___x_3651_);
if (lean_obj_tag(v___x_3652_) == 0)
{
size_t v_sz_3653_; size_t v___x_3654_; lean_object* v___x_3655_; 
lean_dec_ref(v_env_3642_);
v_sz_3653_ = lean_array_size(v_alts_3600_);
v___x_3654_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3600_);
v___x_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_sz_3653_, v___x_3654_, v_alts_3600_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3680_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3680_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3680_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
size_t v___x_3670_; size_t v___x_3671_; uint8_t v___x_3672_; 
v___x_3670_ = lean_ptr_addr(v_alts_3600_);
lean_dec_ref(v_alts_3600_);
v___x_3671_ = lean_ptr_addr(v_a_3656_);
v___x_3672_ = lean_usize_dec_eq(v___x_3670_, v___x_3671_);
if (v___x_3672_ == 0)
{
lean_del_object(v___x_3639_);
lean_dec_ref(v_resultType_3598_);
lean_dec_ref_known(v_code_3288_, 1);
goto v___jp_3660_;
}
else
{
size_t v___x_3673_; size_t v___x_3674_; uint8_t v___x_3675_; 
v___x_3673_ = lean_ptr_addr(v_resultType_3598_);
lean_dec_ref(v_resultType_3598_);
v___x_3674_ = lean_ptr_addr(v_a_3637_);
v___x_3675_ = lean_usize_dec_eq(v___x_3673_, v___x_3674_);
if (v___x_3675_ == 0)
{
lean_del_object(v___x_3639_);
lean_dec_ref_known(v_code_3288_, 1);
goto v___jp_3660_;
}
else
{
uint8_t v___x_3676_; 
v___x_3676_ = l_Lean_instBEqFVarId_beq(v_discr_3599_, v_discr_3599_);
if (v___x_3676_ == 0)
{
lean_del_object(v___x_3639_);
lean_dec_ref_known(v_code_3288_, 1);
goto v___jp_3660_;
}
else
{
lean_object* v___x_3678_; 
lean_del_object(v___x_3658_);
lean_dec(v_a_3656_);
lean_del_object(v___x_3647_);
lean_dec(v_a_3637_);
lean_del_object(v___x_3634_);
lean_dec(v_discr_3599_);
lean_dec(v_typeName_3597_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 0, v_code_3288_);
v___x_3678_ = v___x_3639_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_code_3288_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
v___jp_3660_:
{
lean_object* v___x_3662_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 3, v_a_3656_);
lean_ctor_set(v___x_3634_, 1, v_a_3637_);
v___x_3662_ = v___x_3634_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_typeName_3597_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_a_3637_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_discr_3599_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_a_3656_);
v___x_3662_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set_tag(v___x_3647_, 4);
lean_ctor_set(v___x_3647_, 0, v___x_3662_);
v___x_3664_ = v___x_3647_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3662_);
v___x_3664_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3664_);
v___x_3666_ = v___x_3658_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
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
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3647_);
lean_del_object(v___x_3639_);
lean_dec(v_a_3637_);
lean_del_object(v___x_3634_);
lean_dec_ref(v_alts_3600_);
lean_dec(v_discr_3599_);
lean_dec_ref(v_resultType_3598_);
lean_dec(v_typeName_3597_);
lean_dec_ref_known(v_code_3288_, 1);
v_a_3681_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3655_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3655_);
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
else
{
lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3719_; 
lean_dec_ref_known(v___x_3652_, 1);
lean_del_object(v___x_3647_);
lean_del_object(v___x_3639_);
lean_dec_ref(v_resultType_3598_);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3719_ == 0)
{
lean_object* v_unused_3720_; 
v_unused_3720_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3720_);
v___x_3690_ = v_code_3288_;
v_isShared_3691_ = v_isSharedCheck_3719_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v_code_3288_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3719_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; size_t v_sz_3694_; size_t v___x_3695_; lean_object* v___x_3696_; 
v___x_3692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4));
v___x_3693_ = l_Lean_Name_append(v_typeName_3597_, v___x_3692_);
v_sz_3694_ = lean_array_size(v_alts_3600_);
v___x_3695_ = ((size_t)0ULL);
v___x_3696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_env_3642_, v___x_3628_, v_sz_3694_, v___x_3695_, v_alts_3600_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3710_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3710_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3710_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 3, v_a_3697_);
lean_ctor_set(v___x_3634_, 1, v_a_3637_);
lean_ctor_set(v___x_3634_, 0, v___x_3693_);
v___x_3702_ = v___x_3634_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_a_3637_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_discr_3599_);
lean_ctor_set(v_reuseFailAlloc_3709_, 3, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 0, v___x_3702_);
v___x_3704_ = v___x_3690_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3704_);
v___x_3706_ = v___x_3699_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v___x_3693_);
lean_del_object(v___x_3690_);
lean_dec(v_a_3637_);
lean_del_object(v___x_3634_);
lean_dec(v_discr_3599_);
v_a_3711_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3696_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3696_);
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
}
}
}
else
{
lean_dec(v_val_3644_);
lean_dec_ref(v_env_3642_);
lean_del_object(v___x_3639_);
lean_dec(v_a_3637_);
lean_del_object(v___x_3634_);
lean_dec_ref(v_alts_3600_);
lean_dec(v_discr_3599_);
lean_dec_ref(v_resultType_3598_);
lean_dec(v_typeName_3597_);
lean_dec_ref_known(v_code_3288_, 1);
v___y_3296_ = v_a_3289_;
v___y_3297_ = v_a_3290_;
v___y_3298_ = v_a_3291_;
v___y_3299_ = v_a_3292_;
v___y_3300_ = v_a_3293_;
goto v___jp_3295_;
}
}
else
{
lean_dec(v___x_3643_);
lean_dec_ref(v_env_3642_);
lean_del_object(v___x_3639_);
lean_dec(v_a_3637_);
lean_del_object(v___x_3634_);
lean_dec_ref(v_alts_3600_);
lean_dec(v_discr_3599_);
lean_dec_ref(v_resultType_3598_);
lean_dec(v_typeName_3597_);
lean_dec_ref_known(v_code_3288_, 1);
v___y_3296_ = v_a_3289_;
v___y_3297_ = v_a_3290_;
v___y_3298_ = v_a_3291_;
v___y_3299_ = v_a_3292_;
v___y_3300_ = v_a_3293_;
goto v___jp_3295_;
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3634_);
lean_dec_ref(v_alts_3600_);
lean_dec(v_discr_3599_);
lean_dec_ref(v_resultType_3598_);
lean_dec(v_typeName_3597_);
lean_dec_ref_known(v_code_3288_, 1);
v_a_3723_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3636_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3636_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref(v_cases_3596_);
lean_dec_ref_known(v_code_3288_, 1);
v_a_3736_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3629_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3629_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
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
lean_object* v___x_3744_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3744_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3744_;
}
}
else
{
lean_object* v___x_3745_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3745_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
lean_dec_ref(v_cases_3596_);
return v___x_3745_;
}
}
else
{
lean_object* v___x_3746_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3746_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3746_;
}
}
else
{
lean_object* v___x_3747_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3747_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3747_;
}
}
else
{
lean_object* v___x_3748_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3748_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3748_;
}
}
else
{
lean_object* v___x_3749_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3749_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3749_;
}
}
else
{
lean_object* v___x_3750_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3750_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3750_;
}
}
else
{
lean_object* v___x_3751_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3751_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3751_;
}
}
else
{
lean_object* v___x_3752_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3752_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3596_, v___x_3611_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3752_;
}
}
else
{
lean_object* v___x_3753_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3753_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3596_, v___x_3609_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3753_;
}
}
else
{
lean_object* v___x_3754_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3754_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3596_, v___x_3607_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3754_;
}
}
else
{
lean_object* v___x_3755_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3755_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3596_, v___x_3605_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3755_;
}
}
else
{
lean_object* v___x_3756_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3756_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3756_;
}
}
else
{
lean_object* v___x_3757_; 
lean_dec_ref_known(v_code_3288_, 1);
v___x_3757_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3596_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_);
return v___x_3757_;
}
}
case 5:
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3758_, 0, v_code_3288_);
return v___x_3758_;
}
case 6:
{
lean_object* v_type_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3783_; 
v_type_3759_ = lean_ctor_get(v_code_3288_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3761_ = v_code_3288_;
v_isShared_3762_ = v_isSharedCheck_3783_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_type_3759_);
lean_dec(v_code_3288_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3783_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3759_, v_a_3292_, v_a_3293_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3774_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3766_ = v___x_3763_;
v_isShared_3767_ = v_isSharedCheck_3774_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3763_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3774_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3762_ == 0)
{
lean_ctor_set(v___x_3761_, 0, v_a_3764_);
v___x_3769_ = v___x_3761_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
lean_object* v___x_3771_; 
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v___x_3769_);
v___x_3771_ = v___x_3766_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_del_object(v___x_3761_);
v_a_3775_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3763_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3763_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
default: 
{
lean_object* v_decl_3784_; lean_object* v_k_3785_; 
v_decl_3784_ = lean_ctor_get(v_code_3288_, 0);
v_k_3785_ = lean_ctor_get(v_code_3288_, 1);
lean_inc_ref(v_k_3785_);
lean_inc_ref(v_decl_3784_);
v_decl_3304_ = v_decl_3784_;
v_k_3305_ = v_k_3785_;
v___y_3306_ = v_a_3289_;
v___y_3307_ = v_a_3290_;
v___y_3308_ = v_a_3291_;
v___y_3309_ = v_a_3292_;
v___y_3310_ = v_a_3293_;
goto v___jp_3303_;
}
}
v___jp_3295_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__1, &l_Lean_Compiler_LCNF_Code_toMono___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1);
v___x_3302_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3301_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
return v___x_3302_;
}
v___jp_3303_:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3304_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3313_) == 0)
{
switch(lean_obj_tag(v_code_3288_))
{
case 1:
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3353_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3316_ = v___x_3313_;
v_isShared_3317_ = v_isSharedCheck_3353_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3313_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3353_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v_decl_3318_; lean_object* v_k_3319_; size_t v___x_3320_; size_t v___x_3321_; uint8_t v___x_3322_; 
v_decl_3318_ = lean_ctor_get(v_code_3288_, 0);
v_k_3319_ = lean_ctor_get(v_code_3288_, 1);
v___x_3320_ = lean_ptr_addr(v_k_3319_);
v___x_3321_ = lean_ptr_addr(v_a_3314_);
v___x_3322_ = lean_usize_dec_eq(v___x_3320_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3332_; 
v_isSharedCheck_3332_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3332_ == 0)
{
lean_object* v_unused_3333_; lean_object* v_unused_3334_; 
v_unused_3333_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3333_);
v_unused_3334_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3334_);
v___x_3324_ = v_code_3288_;
v_isShared_3325_ = v_isSharedCheck_3332_;
goto v_resetjp_3323_;
}
else
{
lean_dec(v_code_3288_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3332_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v_a_3314_);
lean_ctor_set(v___x_3324_, 0, v_a_3312_);
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3331_, 1, v_a_3314_);
v___x_3327_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3329_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3327_);
v___x_3329_ = v___x_3316_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
return v___x_3329_;
}
}
}
}
else
{
size_t v___x_3335_; size_t v___x_3336_; uint8_t v___x_3337_; 
v___x_3335_ = lean_ptr_addr(v_decl_3318_);
v___x_3336_ = lean_ptr_addr(v_a_3312_);
v___x_3337_ = lean_usize_dec_eq(v___x_3335_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3347_; 
v_isSharedCheck_3347_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3347_ == 0)
{
lean_object* v_unused_3348_; lean_object* v_unused_3349_; 
v_unused_3348_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3348_);
v_unused_3349_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3349_);
v___x_3339_ = v_code_3288_;
v_isShared_3340_ = v_isSharedCheck_3347_;
goto v_resetjp_3338_;
}
else
{
lean_dec(v_code_3288_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3347_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 1, v_a_3314_);
lean_ctor_set(v___x_3339_, 0, v_a_3312_);
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_a_3314_);
v___x_3342_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3344_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3342_);
v___x_3344_ = v___x_3316_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
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
else
{
lean_object* v___x_3351_; 
lean_dec(v_a_3314_);
lean_dec(v_a_3312_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v_code_3288_);
v___x_3351_ = v___x_3316_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_code_3288_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
case 2:
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3393_; 
v_a_3354_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3356_ = v___x_3313_;
v_isShared_3357_ = v_isSharedCheck_3393_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3313_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3393_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_decl_3358_; lean_object* v_k_3359_; size_t v___x_3360_; size_t v___x_3361_; uint8_t v___x_3362_; 
v_decl_3358_ = lean_ctor_get(v_code_3288_, 0);
v_k_3359_ = lean_ctor_get(v_code_3288_, 1);
v___x_3360_ = lean_ptr_addr(v_k_3359_);
v___x_3361_ = lean_ptr_addr(v_a_3354_);
v___x_3362_ = lean_usize_dec_eq(v___x_3360_, v___x_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3372_; 
v_isSharedCheck_3372_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3372_ == 0)
{
lean_object* v_unused_3373_; lean_object* v_unused_3374_; 
v_unused_3373_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3373_);
v_unused_3374_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3374_);
v___x_3364_ = v_code_3288_;
v_isShared_3365_ = v_isSharedCheck_3372_;
goto v_resetjp_3363_;
}
else
{
lean_dec(v_code_3288_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3372_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 1, v_a_3354_);
lean_ctor_set(v___x_3364_, 0, v_a_3312_);
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_a_3354_);
v___x_3367_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
lean_object* v___x_3369_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3367_);
v___x_3369_ = v___x_3356_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
else
{
size_t v___x_3375_; size_t v___x_3376_; uint8_t v___x_3377_; 
v___x_3375_ = lean_ptr_addr(v_decl_3358_);
v___x_3376_ = lean_ptr_addr(v_a_3312_);
v___x_3377_ = lean_usize_dec_eq(v___x_3375_, v___x_3376_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3387_; 
v_isSharedCheck_3387_ = !lean_is_exclusive(v_code_3288_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; lean_object* v_unused_3389_; 
v_unused_3388_ = lean_ctor_get(v_code_3288_, 1);
lean_dec(v_unused_3388_);
v_unused_3389_ = lean_ctor_get(v_code_3288_, 0);
lean_dec(v_unused_3389_);
v___x_3379_ = v_code_3288_;
v_isShared_3380_ = v_isSharedCheck_3387_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_code_3288_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3387_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 1, v_a_3354_);
lean_ctor_set(v___x_3379_, 0, v_a_3312_);
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3312_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_a_3354_);
v___x_3382_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3384_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3382_);
v___x_3384_ = v___x_3356_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v_a_3354_);
lean_dec(v_a_3312_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v_code_3288_);
v___x_3391_ = v___x_3356_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_code_3288_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
default: 
{
lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v_a_3312_);
lean_dec_ref(v_code_3288_);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v___x_3313_, 0);
lean_dec(v_unused_3403_);
v___x_3395_ = v___x_3313_;
v_isShared_3396_ = v_isSharedCheck_3402_;
goto v_resetjp_3394_;
}
else
{
lean_dec(v___x_3313_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3402_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
v___x_3397_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3398_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3397_);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 0, v___x_3398_);
v___x_3400_ = v___x_3395_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
else
{
lean_dec(v_a_3312_);
lean_dec_ref(v_code_3288_);
return v___x_3313_;
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_k_3305_);
lean_dec_ref(v_code_3288_);
v_a_3404_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3311_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3311_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_params_3793_; lean_object* v_type_3794_; lean_object* v_value_3795_; uint8_t v___x_3796_; lean_object* v___x_3797_; 
v_params_3793_ = lean_ctor_get(v_decl_3786_, 2);
v_type_3794_ = lean_ctor_get(v_decl_3786_, 3);
v_value_3795_ = lean_ctor_get(v_decl_3786_, 4);
v___x_3796_ = 0;
lean_inc_ref(v_type_3794_);
v___x_3797_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3794_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; size_t v_sz_3799_; size_t v___x_3800_; lean_object* v___x_3801_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v_sz_3799_ = lean_array_size(v_params_3793_);
v___x_3800_ = ((size_t)0ULL);
lean_inc_ref(v_params_3793_);
v___x_3801_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_3799_, v___x_3800_, v_params_3793_, v_a_3787_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
lean_inc_ref(v_value_3795_);
v___x_3803_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_3795_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v___x_3805_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3796_, v_decl_3786_, v_a_3798_, v_a_3802_, v_a_3804_, v_a_3789_);
return v___x_3805_;
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec(v_a_3802_);
lean_dec(v_a_3798_);
lean_dec_ref(v_decl_3786_);
v_a_3806_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3803_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3803_);
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
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_a_3798_);
lean_dec_ref(v_decl_3786_);
v_a_3814_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3801_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3801_);
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
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_decl_3786_);
v_a_3822_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3797_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3797_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_sz_3838_, lean_object* v_i_3839_, lean_object* v_bs_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
size_t v_sz_boxed_3847_; size_t v_i_boxed_3848_; lean_object* v_res_3849_; 
v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3838_);
lean_dec(v_sz_3838_);
v_i_boxed_3848_ = lean_unbox_usize(v_i_3839_);
lean_dec(v_i_3839_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_sz_boxed_3847_, v_i_boxed_3848_, v_bs_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_3858_, lean_object* v_uintName_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_3858_, v_uintName_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
lean_dec(v_a_3876_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v___x_3907_, lean_object* v___x_3908_, lean_object* v_sz_3909_, lean_object* v_i_3910_, lean_object* v_bs_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
uint8_t v___x_33843__boxed_3918_; size_t v_sz_boxed_3919_; size_t v_i_boxed_3920_; lean_object* v_res_3921_; 
v___x_33843__boxed_3918_ = lean_unbox(v___x_3908_);
v_sz_boxed_3919_ = lean_unbox_usize(v_sz_3909_);
lean_dec(v_sz_3909_);
v_i_boxed_3920_ = lean_unbox_usize(v_i_3910_);
lean_dec(v_i_3910_);
v_res_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v___x_3907_, v___x_33843__boxed_3918_, v_sz_boxed_3919_, v_i_boxed_3920_, v_bs_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_3946_, lean_object* v_c_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_3946_, v_c_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_);
lean_dec(v_a_3952_);
lean_dec_ref(v_a_3951_);
lean_dec(v_a_3950_);
lean_dec_ref(v_a_3949_);
lean_dec(v_a_3948_);
lean_dec_ref(v_info_3946_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_3955_, lean_object* v_sz_3956_, lean_object* v_i_3957_, lean_object* v_bs_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
size_t v_sz_boxed_3965_; size_t v_i_boxed_3966_; lean_object* v_res_3967_; 
v_sz_boxed_3965_ = lean_unbox_usize(v_sz_3956_);
lean_dec(v_sz_3956_);
v_i_boxed_3966_ = lean_unbox_usize(v_i_3957_);
lean_dec(v_i_3957_);
v_res_3967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3955_, v_sz_boxed_3965_, v_i_boxed_3966_, v_bs_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_){
_start:
{
lean_object* v_res_3975_; 
v_res_3975_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
lean_dec(v_a_3973_);
lean_dec_ref(v_a_3972_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_c_3968_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_3976_, lean_object* v_sz_3977_, lean_object* v_i_3978_, lean_object* v_bs_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
size_t v_sz_boxed_3986_; size_t v_i_boxed_3987_; lean_object* v_res_3988_; 
v_sz_boxed_3986_ = lean_unbox_usize(v_sz_3977_);
lean_dec(v_sz_3977_);
v_i_boxed_3987_ = lean_unbox_usize(v_i_3978_);
lean_dec(v_i_3978_);
v_res_3988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3976_, v_sz_boxed_3986_, v_i_boxed_3987_, v_bs_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_3997_, lean_object* v_x_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_3997_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4006_, lean_object* v_x_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4006_, v_x_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4015_, lean_object* v_x_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4015_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4024_, lean_object* v_x_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4024_, v_x_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec_ref(v_c_4024_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4033_, lean_object* v_x_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4033_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4042_, lean_object* v_x_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4042_, v_x_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
lean_dec(v_a_4046_);
lean_dec_ref(v_a_4045_);
lean_dec(v_a_4044_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4051_, lean_object* v_x_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4051_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4060_, lean_object* v_x_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4060_, v_x_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4069_, lean_object* v_x_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4069_, v_a_4071_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4078_, lean_object* v_x_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_res_4086_; 
v_res_4086_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4078_, v_x_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_);
lean_dec(v_a_4084_);
lean_dec_ref(v_a_4083_);
lean_dec(v_a_4082_);
lean_dec_ref(v_a_4081_);
lean_dec(v_a_4080_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4087_, lean_object* v_x_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4087_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4096_, lean_object* v_x_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4096_, v_x_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
lean_dec(v_a_4102_);
lean_dec_ref(v_a_4101_);
lean_dec(v_a_4100_);
lean_dec_ref(v_a_4099_);
lean_dec(v_a_4098_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4105_, lean_object* v_x_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4105_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4114_, lean_object* v_x_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4114_, v_x_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
lean_dec(v_a_4118_);
lean_dec_ref(v_a_4117_);
lean_dec(v_a_4116_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4123_, lean_object* v_x_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4123_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4132_, lean_object* v_x_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4132_, v_x_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4141_, lean_object* v_uintName_4142_, lean_object* v_x_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4141_, v_uintName_4142_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4151_, lean_object* v_uintName_4152_, lean_object* v_x_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4151_, v_uintName_4152_, v_x_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4161_, lean_object* v_x_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4161_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4170_, lean_object* v_x_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4170_, v_x_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4179_, lean_object* v_x_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4179_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4188_, lean_object* v_x_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_res_4196_; 
v_res_4196_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4188_, v_x_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_);
lean_dec(v_a_4194_);
lean_dec_ref(v_a_4193_);
lean_dec(v_a_4192_);
lean_dec_ref(v_a_4191_);
lean_dec(v_a_4190_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4197_, size_t v_i_4198_, lean_object* v_bs_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4197_, v_i_4198_, v_bs_4199_, v___y_4200_, v___y_4202_, v___y_4203_, v___y_4204_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4207_, lean_object* v_i_4208_, lean_object* v_bs_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
size_t v_sz_boxed_4216_; size_t v_i_boxed_4217_; lean_object* v_res_4218_; 
v_sz_boxed_4216_ = lean_unbox_usize(v_sz_4207_);
lean_dec(v_sz_4207_);
v_i_boxed_4217_ = lean_unbox_usize(v_i_4208_);
lean_dec(v_i_4208_);
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4216_, v_i_boxed_4217_, v_bs_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4219_, lean_object* v_v_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
if (lean_obj_tag(v_v_4220_) == 0)
{
lean_object* v_code_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4251_; 
v_code_4227_ = lean_ctor_get(v_v_4220_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v_v_4220_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4229_ = v_v_4220_;
v_isShared_4230_ = v_isSharedCheck_4251_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_code_4227_);
lean_dec(v_v_4220_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4251_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; 
lean_inc(v___y_4225_);
lean_inc_ref(v___y_4224_);
lean_inc(v___y_4223_);
lean_inc_ref(v___y_4222_);
lean_inc(v___y_4221_);
v___x_4231_ = lean_apply_7(v_f_4219_, v_code_4227_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, lean_box(0));
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4242_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4234_ = v___x_4231_;
v_isShared_4235_ = v_isSharedCheck_4242_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4242_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v_a_4232_);
v___x_4237_ = v___x_4229_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4239_; 
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v___x_4237_);
v___x_4239_ = v___x_4234_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_del_object(v___x_4229_);
v_a_4243_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4231_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4231_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
else
{
lean_object* v___x_4252_; 
lean_dec_ref(v_f_4219_);
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v_v_4220_);
return v___x_4252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4253_, lean_object* v_v_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4253_, v_v_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4262_, lean_object* v_f_4263_, lean_object* v_v_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4263_, v_v_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4272_, lean_object* v_f_4273_, lean_object* v_v_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
uint8_t v_pu_boxed_4281_; lean_object* v_res_4282_; 
v_pu_boxed_4281_ = lean_unbox(v_pu_4272_);
v_res_4282_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4281_, v_f_4273_, v_v_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_){
_start:
{
lean_object* v_toSignature_4291_; lean_object* v_value_4292_; uint8_t v_recursive_4293_; lean_object* v_inlineAttr_x3f_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4364_; 
v_toSignature_4291_ = lean_ctor_get(v_decl_4284_, 0);
v_value_4292_ = lean_ctor_get(v_decl_4284_, 1);
v_recursive_4293_ = lean_ctor_get_uint8(v_decl_4284_, sizeof(void*)*3);
v_inlineAttr_x3f_4294_ = lean_ctor_get(v_decl_4284_, 2);
v_isSharedCheck_4364_ = !lean_is_exclusive(v_decl_4284_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4296_ = v_decl_4284_;
v_isShared_4297_ = v_isSharedCheck_4364_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_inlineAttr_x3f_4294_);
lean_inc(v_value_4292_);
lean_inc(v_toSignature_4291_);
lean_dec(v_decl_4284_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4364_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v_name_4298_; lean_object* v_type_4299_; lean_object* v_params_4300_; uint8_t v_safe_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4362_; 
v_name_4298_ = lean_ctor_get(v_toSignature_4291_, 0);
v_type_4299_ = lean_ctor_get(v_toSignature_4291_, 2);
v_params_4300_ = lean_ctor_get(v_toSignature_4291_, 3);
v_safe_4301_ = lean_ctor_get_uint8(v_toSignature_4291_, sizeof(void*)*4);
v_isSharedCheck_4362_ = !lean_is_exclusive(v_toSignature_4291_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; 
v_unused_4363_ = lean_ctor_get(v_toSignature_4291_, 1);
lean_dec(v_unused_4363_);
v___x_4303_ = v_toSignature_4291_;
v_isShared_4304_ = v_isSharedCheck_4362_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_params_4300_);
lean_inc(v_type_4299_);
lean_inc(v_name_4298_);
lean_dec(v_toSignature_4291_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4362_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___f_4305_; lean_object* v___x_4306_; 
v___f_4305_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4306_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4299_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; size_t v_sz_4308_; size_t v___x_4309_; lean_object* v___x_4310_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
v_sz_4308_ = lean_array_size(v_params_4300_);
v___x_4309_ = ((size_t)0ULL);
v___x_4310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4308_, v___x_4309_, v_params_4300_, v_a_4285_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref_known(v___x_4310_, 1);
v___x_4312_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4305_, v_value_4292_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; lean_object* v___x_4316_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v___x_4314_ = lean_box(0);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 3, v_a_4311_);
lean_ctor_set(v___x_4303_, 2, v_a_4307_);
lean_ctor_set(v___x_4303_, 1, v___x_4314_);
v___x_4316_ = v___x_4303_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_name_4298_);
lean_ctor_set(v_reuseFailAlloc_4337_, 1, v___x_4314_);
lean_ctor_set(v_reuseFailAlloc_4337_, 2, v_a_4307_);
lean_ctor_set(v_reuseFailAlloc_4337_, 3, v_a_4311_);
lean_ctor_set_uint8(v_reuseFailAlloc_4337_, sizeof(void*)*4, v_safe_4301_);
v___x_4316_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4318_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 1, v_a_4313_);
lean_ctor_set(v___x_4296_, 0, v___x_4316_);
v___x_4318_ = v___x_4296_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4316_);
lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_a_4313_);
lean_ctor_set(v_reuseFailAlloc_4336_, 2, v_inlineAttr_x3f_4294_);
lean_ctor_set_uint8(v_reuseFailAlloc_4336_, sizeof(void*)*3, v_recursive_4293_);
v___x_4318_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
lean_object* v___x_4319_; 
lean_inc_ref(v___x_4318_);
v___x_4319_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4318_, v_a_4289_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4326_ == 0)
{
lean_object* v_unused_4327_; 
v_unused_4327_ = lean_ctor_get(v___x_4319_, 0);
lean_dec(v_unused_4327_);
v___x_4321_ = v___x_4319_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_dec(v___x_4319_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 0, v___x_4318_);
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4318_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v___x_4318_);
v_a_4328_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4319_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4319_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec(v_a_4311_);
lean_dec(v_a_4307_);
lean_del_object(v___x_4303_);
lean_dec(v_name_4298_);
lean_del_object(v___x_4296_);
lean_dec(v_inlineAttr_x3f_4294_);
v_a_4338_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4312_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4312_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec(v_a_4307_);
lean_del_object(v___x_4303_);
lean_dec(v_name_4298_);
lean_del_object(v___x_4296_);
lean_dec(v_inlineAttr_x3f_4294_);
lean_dec_ref(v_value_4292_);
v_a_4346_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4310_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4310_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_del_object(v___x_4303_);
lean_dec_ref(v_params_4300_);
lean_dec(v_name_4298_);
lean_del_object(v___x_4296_);
lean_dec(v_inlineAttr_x3f_4294_);
lean_dec_ref(v_value_4292_);
v_a_4354_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4306_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4306_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
return v_res_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4379_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4380_ = lean_st_mk_ref(v___x_4379_);
v___x_4381_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4373_, v___x_4380_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4390_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4384_ = v___x_4381_;
v_isShared_4385_ = v_isSharedCheck_4390_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4381_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4390_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4388_; 
v___x_4386_ = lean_st_ref_get(v___x_4380_);
lean_dec(v___x_4380_);
lean_dec(v___x_4386_);
if (v_isShared_4385_ == 0)
{
v___x_4388_ = v___x_4384_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4382_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
else
{
lean_dec(v___x_4380_);
return v___x_4381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_){
_start:
{
lean_object* v_res_4397_; 
v_res_4397_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
return v_res_4397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4398_, size_t v_i_4399_, lean_object* v_bs_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
uint8_t v___x_4406_; 
v___x_4406_ = lean_usize_dec_lt(v_i_4399_, v_sz_4398_);
if (v___x_4406_ == 0)
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v_bs_4400_);
return v___x_4407_;
}
else
{
lean_object* v_v_4408_; lean_object* v___x_4409_; lean_object* v_bs_x27_4410_; lean_object* v___x_4411_; 
v_v_4408_ = lean_array_uget(v_bs_4400_, v_i_4399_);
v___x_4409_ = lean_unsigned_to_nat(0u);
v_bs_x27_4410_ = lean_array_uset(v_bs_4400_, v_i_4399_, v___x_4409_);
v___x_4411_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4408_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; size_t v___x_4413_; size_t v___x_4414_; lean_object* v___x_4415_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v___x_4413_ = ((size_t)1ULL);
v___x_4414_ = lean_usize_add(v_i_4399_, v___x_4413_);
v___x_4415_ = lean_array_uset(v_bs_x27_4410_, v_i_4399_, v_a_4412_);
v_i_4399_ = v___x_4414_;
v_bs_4400_ = v___x_4415_;
goto _start;
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec_ref(v_bs_x27_4410_);
v_a_4417_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4411_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4411_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4425_, lean_object* v_i_4426_, lean_object* v_bs_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
size_t v_sz_boxed_4433_; size_t v_i_boxed_4434_; lean_object* v_res_4435_; 
v_sz_boxed_4433_ = lean_unbox_usize(v_sz_4425_);
lean_dec(v_sz_4425_);
v_i_boxed_4434_ = lean_unbox_usize(v_i_4426_);
lean_dec(v_i_4426_);
v_res_4435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4433_, v_i_boxed_4434_, v_bs_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_sz_4442_; size_t v___x_4443_; lean_object* v___x_4444_; 
v_sz_4442_ = lean_array_size(v_x_4436_);
v___x_4443_ = ((size_t)0ULL);
v___x_4444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4442_, v___x_4443_, v_x_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4534_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4535_ = 1;
v___x_4536_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4537_ = l_Lean_registerTraceClass(v___x_4534_, v___x_4535_, v___x_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4539_;
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
