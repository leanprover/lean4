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
static const lean_string_object l_Lean_Compiler_LCNF_Code_toMono___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__16_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__16_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__17_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__18_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ByteArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 14, 5, 86, 33, 2, 113, 205)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__19_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FloatArray"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 8, 149, 159, 140, 65, 145, 29)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__20_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__21_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 69, 114, 85, 163, 177, 220, 67)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__22_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 232, 182, 48, 64, 193, 160, 231)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Thunk"};
static const lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 24, 139, 128, 157, 117, 211, 220)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__24_value;
static const lean_string_object l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Task"};
static const lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Code_toMono___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 131, 95, 48, 7, 243, 177, 18)}};
static const lean_object* l_Lean_Compiler_LCNF_Code_toMono___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_Code_toMono___closed__25_value;
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
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_30910__overap_1331_; lean_object* v___x_1332_; 
v___x_1328_ = l_StateRefT_x27_instMonad___redArg(v___x_1327_);
v___x_1329_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1330_ = l_instInhabitedOfMonad___redArg(v___x_1328_, v___x_1329_);
v___x_30910__overap_1331_ = lean_panic_fn_borrowed(v___x_1330_, v_msg_1272_);
lean_dec(v___x_1330_);
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
lean_inc(v___y_1273_);
v___x_1332_ = lean_apply_6(v___x_30910__overap_1331_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, lean_box(0));
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
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_30628__overap_1413_; lean_object* v___x_1414_; 
v___x_1410_ = l_StateRefT_x27_instMonad___redArg(v___x_1409_);
v___x_1411_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1412_ = l_instInhabitedOfMonad___redArg(v___x_1410_, v___x_1411_);
v___x_30628__overap_1413_ = lean_panic_fn_borrowed(v___x_1412_, v_msg_1354_);
lean_dec(v___x_1412_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
lean_inc(v___y_1357_);
lean_inc_ref(v___y_1356_);
lean_inc(v___y_1355_);
v___x_1414_ = lean_apply_6(v___x_30628__overap_1413_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, lean_box(0));
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
v___x_1480_ = lean_unsigned_to_nat(365u);
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
v___x_1488_ = lean_unsigned_to_nat(658u);
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
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1562_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1563_ = lean_unsigned_to_nat(2u);
v___x_1564_ = lean_unsigned_to_nat(304u);
v___x_1565_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1566_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1567_ = l_mkPanicMessageWithDecl(v___x_1566_, v___x_1565_, v___x_1564_, v___x_1563_, v___x_1562_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1569_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1570_ = lean_unsigned_to_nat(2u);
v___x_1571_ = lean_unsigned_to_nat(305u);
v___x_1572_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1573_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1574_ = l_mkPanicMessageWithDecl(v___x_1573_, v___x_1572_, v___x_1571_, v___x_1570_, v___x_1569_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3(void){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1576_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1577_ = lean_unsigned_to_nat(41u);
v___x_1578_ = lean_unsigned_to_nat(303u);
v___x_1579_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1580_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1581_ = l_mkPanicMessageWithDecl(v___x_1580_, v___x_1579_, v___x_1578_, v___x_1577_, v___x_1576_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1582_, lean_object* v_c_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_discr_1590_; lean_object* v_alts_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1669_; 
v_discr_1590_ = lean_ctor_get(v_c_1583_, 2);
v_alts_1591_ = lean_ctor_get(v_c_1583_, 3);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_c_1583_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; lean_object* v_unused_1671_; 
v_unused_1670_ = lean_ctor_get(v_c_1583_, 1);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_c_1583_, 0);
lean_dec(v_unused_1671_);
v___x_1593_ = v_c_1583_;
v_isShared_1594_ = v_isSharedCheck_1669_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_alts_1591_);
lean_inc(v_discr_1590_);
lean_dec(v_c_1583_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1669_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = lean_array_get_size(v_alts_1591_);
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_dec_eq(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_del_object(v___x_1593_);
lean_dec_ref(v_alts_1591_);
lean_dec(v_discr_1590_);
v___x_1598_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1599_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1598_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1599_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_array_get(v___x_1600_, v_alts_1591_, v___x_1601_);
lean_dec_ref(v_alts_1591_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_ctorName_1603_; lean_object* v_params_1604_; lean_object* v_code_1605_; lean_object* v_ctorName_1606_; lean_object* v_fieldIdx_1607_; uint8_t v___x_1608_; 
v_ctorName_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_ctorName_1603_);
v_params_1604_ = lean_ctor_get(v___x_1602_, 1);
lean_inc_ref(v_params_1604_);
v_code_1605_ = lean_ctor_get(v___x_1602_, 2);
lean_inc_ref(v_code_1605_);
lean_dec_ref_known(v___x_1602_, 3);
v_ctorName_1606_ = lean_ctor_get(v_info_1582_, 0);
v_fieldIdx_1607_ = lean_ctor_get(v_info_1582_, 2);
v___x_1608_ = lean_name_eq(v_ctorName_1603_, v_ctorName_1606_);
lean_dec(v_ctorName_1603_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec_ref(v_code_1605_);
lean_dec_ref(v_params_1604_);
lean_del_object(v___x_1593_);
lean_dec(v_discr_1590_);
v___x_1609_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1610_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1609_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_array_get_size(v_params_1604_);
v___x_1612_ = lean_nat_dec_lt(v_fieldIdx_1607_, v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec_ref(v_code_1605_);
lean_dec_ref(v_params_1604_);
lean_del_object(v___x_1593_);
lean_dec(v_discr_1590_);
v___x_1613_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1614_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1613_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1614_;
}
else
{
uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v_p_1617_; lean_object* v___x_1618_; 
v___x_1615_ = 0;
v___x_1616_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v_p_1617_ = lean_array_get(v___x_1616_, v_params_1604_, v_fieldIdx_1607_);
v___x_1618_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1615_, v_params_1604_, v_a_1586_);
lean_dec_ref(v_params_1604_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_fvarId_1619_; lean_object* v_binderName_1620_; lean_object* v_type_1621_; lean_object* v___x_1622_; 
lean_dec_ref_known(v___x_1618_, 1);
v_fvarId_1619_ = lean_ctor_get(v_p_1617_, 0);
lean_inc(v_fvarId_1619_);
v_binderName_1620_ = lean_ctor_get(v_p_1617_, 1);
lean_inc(v_binderName_1620_);
v_type_1621_ = lean_ctor_get(v_p_1617_, 2);
lean_inc_ref(v_type_1621_);
lean_dec(v_p_1617_);
v___x_1622_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1621_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1624_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_1625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1625_, 0, v_discr_1590_);
lean_ctor_set(v___x_1625_, 1, v___x_1624_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 3, v___x_1625_);
lean_ctor_set(v___x_1593_, 2, v_a_1623_);
lean_ctor_set(v___x_1593_, 1, v_binderName_1620_);
lean_ctor_set(v___x_1593_, 0, v_fvarId_1619_);
v___x_1627_ = v___x_1593_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_fvarId_1619_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_binderName_1620_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_a_1623_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v_lctx_1629_; lean_object* v_nextIdx_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1649_; 
v___x_1628_ = lean_st_ref_take(v_a_1586_);
v_lctx_1629_ = lean_ctor_get(v___x_1628_, 0);
v_nextIdx_1630_ = lean_ctor_get(v___x_1628_, 1);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1632_ = v___x_1628_;
v_isShared_1633_ = v_isSharedCheck_1649_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_nextIdx_1630_);
lean_inc(v_lctx_1629_);
lean_dec(v___x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1649_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_inc_ref(v___x_1627_);
v___x_1634_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1615_, v_lctx_1629_, v___x_1627_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_nextIdx_1630_);
v___x_1636_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_st_ref_put(v_a_1586_, v___x_1636_);
v___x_1638_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1605_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1627_);
lean_ctor_set(v___x_1643_, 1, v_a_1639_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
else
{
lean_dec_ref(v___x_1627_);
return v___x_1638_;
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_binderName_1620_);
lean_dec(v_fvarId_1619_);
lean_dec_ref(v_code_1605_);
lean_del_object(v___x_1593_);
lean_dec(v_discr_1590_);
v_a_1651_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1622_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1622_);
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
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec(v_p_1617_);
lean_dec_ref(v_code_1605_);
lean_del_object(v___x_1593_);
lean_dec(v_discr_1590_);
v_a_1659_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1618_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1618_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec(v___x_1602_);
lean_del_object(v___x_1593_);
lean_dec(v_discr_1590_);
v___x_1667_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_1668_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1667_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_bs_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
uint8_t v___x_1681_; 
v___x_1681_ = lean_usize_dec_lt(v_i_1673_, v_sz_1672_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_bs_1674_);
return v___x_1682_;
}
else
{
lean_object* v_v_1683_; lean_object* v___x_1684_; lean_object* v_bs_x27_1685_; lean_object* v_a_1687_; 
v_v_1683_ = lean_array_uget(v_bs_1674_, v_i_1673_);
v___x_1684_ = lean_unsigned_to_nat(0u);
v_bs_x27_1685_ = lean_array_uset(v_bs_1674_, v_i_1673_, v___x_1684_);
if (lean_obj_tag(v_v_1683_) == 0)
{
lean_object* v_params_1692_; lean_object* v_code_1693_; uint8_t v___x_1694_; size_t v_sz_1695_; size_t v___x_1696_; lean_object* v___x_1697_; 
v_params_1692_ = lean_ctor_get(v_v_1683_, 1);
v_code_1693_ = lean_ctor_get(v_v_1683_, 2);
v___x_1694_ = 0;
v_sz_1695_ = lean_array_size(v_params_1692_);
v___x_1696_ = ((size_t)0ULL);
lean_inc_ref(v_params_1692_);
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1695_, v___x_1696_, v_params_1692_, v___y_1675_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1697_, 1);
lean_inc_ref(v_code_1693_);
v___x_1699_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1693_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1694_, v_v_1683_, v_a_1698_, v_a_1700_);
v_a_1687_ = v___x_1701_;
goto v___jp_1686_;
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v_a_1698_);
lean_dec_ref_known(v_v_1683_, 3);
lean_dec_ref(v_bs_x27_1685_);
v_a_1702_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1699_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1699_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_1683_, 3);
lean_dec_ref(v_bs_x27_1685_);
return v___x_1697_;
}
}
else
{
lean_object* v_code_1710_; lean_object* v___x_1711_; 
v_code_1710_ = lean_ctor_get(v_v_1683_, 0);
lean_inc_ref(v_code_1710_);
v___x_1711_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1710_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
v___x_1713_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1683_, v_a_1712_);
v_a_1687_ = v___x_1713_;
goto v___jp_1686_;
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref_known(v_v_1683_, 1);
lean_dec_ref(v_bs_x27_1685_);
v_a_1714_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1711_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1711_);
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
v___jp_1686_:
{
size_t v___x_1688_; size_t v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = ((size_t)1ULL);
v___x_1689_ = lean_usize_add(v_i_1673_, v___x_1688_);
v___x_1690_ = lean_array_uset(v_bs_x27_1685_, v_i_1673_, v_a_1687_);
v_i_1673_ = v___x_1689_;
v_bs_1674_ = v___x_1690_;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__1));
v___x_1727_ = lean_unsigned_to_nat(70u);
v___x_1728_ = lean_unsigned_to_nat(375u);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__0));
v___x_1730_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1731_ = l_mkPanicMessageWithDecl(v___x_1730_, v___x_1729_, v___x_1728_, v___x_1727_, v___x_1726_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(lean_object* v___x_1732_, uint8_t v___x_1733_, size_t v_sz_1734_, size_t v_i_1735_, lean_object* v_bs_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1735_, v_sz_1734_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref(v___x_1732_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_bs_1736_);
return v___x_1744_;
}
else
{
lean_object* v_v_1745_; lean_object* v___x_1746_; lean_object* v_bs_x27_1747_; lean_object* v_a_1749_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; 
v_v_1745_ = lean_array_uget(v_bs_1736_, v_i_1735_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v_bs_x27_1747_ = lean_array_uset(v_bs_1736_, v_i_1735_, v___x_1746_);
if (lean_obj_tag(v_v_1745_) == 0)
{
lean_object* v_ctorName_1771_; lean_object* v_params_1772_; lean_object* v_code_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1811_; 
v_ctorName_1771_ = lean_ctor_get(v_v_1745_, 0);
v_params_1772_ = lean_ctor_get(v_v_1745_, 1);
v_code_1773_ = lean_ctor_get(v_v_1745_, 2);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_v_1745_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1775_ = v_v_1745_;
v_isShared_1776_ = v_isSharedCheck_1811_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_code_1773_);
lean_inc(v_params_1772_);
lean_inc(v_ctorName_1771_);
lean_dec(v_v_1745_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1811_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4));
v___x_1778_ = l_Lean_Name_append(v_ctorName_1771_, v___x_1777_);
lean_inc(v___x_1778_);
lean_inc_ref(v___x_1732_);
v___x_1779_ = l_Lean_Environment_find_x3f(v___x_1732_, v___x_1778_, v___x_1733_);
if (lean_obj_tag(v___x_1779_) == 1)
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1779_, 1);
if (lean_obj_tag(v_val_1780_) == 6)
{
lean_object* v_val_1781_; lean_object* v_toConstantVal_1782_; lean_object* v_numParams_1783_; lean_object* v_numFields_1784_; lean_object* v_type_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_val_1781_ = lean_ctor_get(v_val_1780_, 0);
lean_inc_ref(v_val_1781_);
lean_dec_ref_known(v_val_1780_, 1);
v_toConstantVal_1782_ = lean_ctor_get(v_val_1781_, 0);
lean_inc_ref(v_toConstantVal_1782_);
v_numParams_1783_ = lean_ctor_get(v_val_1781_, 3);
lean_inc(v_numParams_1783_);
v_numFields_1784_ = lean_ctor_get(v_val_1781_, 4);
lean_inc(v_numFields_1784_);
lean_dec_ref(v_val_1781_);
v_type_1785_ = lean_ctor_get(v_toConstantVal_1782_, 2);
lean_inc_ref(v_type_1785_);
lean_dec_ref(v_toConstantVal_1782_);
v___x_1786_ = lean_array_get_size(v_params_1772_);
v___x_1787_ = lean_nat_sub(v_numFields_1784_, v___x_1786_);
lean_dec(v_numFields_1784_);
v___x_1788_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_1785_, v_numParams_1783_, v___x_1787_, v_params_1772_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec_ref(v_params_1772_);
lean_dec(v___x_1787_);
lean_dec(v_numParams_1783_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1773_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 2, v_a_1791_);
lean_ctor_set(v___x_1775_, 1, v_a_1789_);
lean_ctor_set(v___x_1775_, 0, v___x_1778_);
v___x_1793_ = v___x_1775_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_a_1789_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_a_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
v_a_1749_ = v___x_1793_;
goto v___jp_1748_;
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_a_1789_);
lean_dec(v___x_1778_);
lean_del_object(v___x_1775_);
lean_dec_ref(v_bs_x27_1747_);
lean_dec_ref(v___x_1732_);
v_a_1795_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1790_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1790_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec(v___x_1778_);
lean_del_object(v___x_1775_);
lean_dec_ref(v_code_1773_);
lean_dec_ref(v_bs_x27_1747_);
lean_dec_ref(v___x_1732_);
v_a_1803_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1788_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1788_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_dec(v_val_1780_);
lean_dec(v___x_1778_);
lean_del_object(v___x_1775_);
lean_dec_ref(v_code_1773_);
lean_dec_ref(v_params_1772_);
v___y_1755_ = v___y_1737_;
v___y_1756_ = v___y_1738_;
v___y_1757_ = v___y_1739_;
v___y_1758_ = v___y_1740_;
v___y_1759_ = v___y_1741_;
goto v___jp_1754_;
}
}
else
{
lean_dec(v___x_1779_);
lean_dec(v___x_1778_);
lean_del_object(v___x_1775_);
lean_dec_ref(v_code_1773_);
lean_dec_ref(v_params_1772_);
v___y_1755_ = v___y_1737_;
v___y_1756_ = v___y_1738_;
v___y_1757_ = v___y_1739_;
v___y_1758_ = v___y_1740_;
v___y_1759_ = v___y_1741_;
goto v___jp_1754_;
}
}
}
else
{
lean_object* v_code_1812_; lean_object* v___x_1813_; 
v_code_1812_ = lean_ctor_get(v_v_1745_, 0);
lean_inc_ref(v_code_1812_);
v___x_1813_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1812_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1815_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
v___x_1815_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1745_, v_a_1814_);
v_a_1749_ = v___x_1815_;
goto v___jp_1748_;
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref_known(v_v_1745_, 1);
lean_dec_ref(v_bs_x27_1747_);
lean_dec_ref(v___x_1732_);
v_a_1816_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1813_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1813_);
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
v___jp_1748_:
{
size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1735_, v___x_1750_);
v___x_1752_ = lean_array_uset(v_bs_x27_1747_, v_i_1735_, v_a_1749_);
v_i_1735_ = v___x_1751_;
v_bs_1736_ = v___x_1752_;
goto _start;
}
v___jp_1754_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__2);
v___x_1761_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_1760_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v_a_1749_ = v_a_1762_;
goto v___jp_1748_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v_bs_x27_1747_);
lean_dec_ref(v___x_1732_);
v_a_1763_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1761_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
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
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1825_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1826_ = lean_unsigned_to_nat(2u);
v___x_1827_ = lean_unsigned_to_nat(291u);
v___x_1828_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1829_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1830_ = l_mkPanicMessageWithDecl(v___x_1829_, v___x_1828_, v___x_1827_, v___x_1826_, v___x_1825_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_unsigned_to_nat(2u);
v___x_1837_ = lean_mk_empty_array_with_capacity(v___x_1836_);
v___x_1838_ = lean_array_push(v___x_1837_, v___x_1835_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1839_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1840_ = lean_unsigned_to_nat(34u);
v___x_1841_ = lean_unsigned_to_nat(292u);
v___x_1842_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1843_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1844_ = l_mkPanicMessageWithDecl(v___x_1843_, v___x_1842_, v___x_1841_, v___x_1840_, v___x_1839_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v_discr_1852_; lean_object* v_alts_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1922_; 
v_discr_1852_ = lean_ctor_get(v_c_1845_, 2);
v_alts_1853_ = lean_ctor_get(v_c_1845_, 3);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_c_1845_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; lean_object* v_unused_1924_; 
v_unused_1923_ = lean_ctor_get(v_c_1845_, 1);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_c_1845_, 0);
lean_dec(v_unused_1924_);
v___x_1855_ = v_c_1845_;
v_isShared_1856_ = v_isSharedCheck_1922_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_alts_1853_);
lean_inc(v_discr_1852_);
lean_dec(v_c_1845_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1922_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v___x_1857_ = lean_array_get_size(v_alts_1853_);
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_dec_eq(v___x_1857_, v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_del_object(v___x_1855_);
lean_dec_ref(v_alts_1853_);
lean_dec(v_discr_1852_);
v___x_1860_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_1861_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1860_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = lean_array_get(v___x_1862_, v_alts_1853_, v___x_1863_);
lean_dec_ref(v_alts_1853_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_params_1865_; lean_object* v_code_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1918_; 
v_params_1865_ = lean_ctor_get(v___x_1864_, 1);
v_code_1866_ = lean_ctor_get(v___x_1864_, 2);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1864_, 0);
lean_dec(v_unused_1919_);
v___x_1868_ = v___x_1864_;
v_isShared_1869_ = v_isSharedCheck_1918_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_code_1866_);
lean_inc(v_params_1865_);
lean_dec(v___x_1864_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1918_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = 0;
v___x_1871_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1872_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1870_, v_params_1865_, v_a_1848_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v___x_1873_; lean_object* v_fvarId_1874_; lean_object* v_binderName_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
lean_dec_ref_known(v___x_1872_, 1);
v___x_1873_ = lean_array_get(v___x_1871_, v_params_1865_, v___x_1863_);
lean_dec_ref(v_params_1865_);
v_fvarId_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_fvarId_1874_);
v_binderName_1875_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_binderName_1875_);
lean_dec(v___x_1873_);
v___x_1876_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1877_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_1878_ = lean_box(0);
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_discr_1852_);
v___x_1880_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1881_ = lean_array_push(v___x_1880_, v___x_1879_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set_tag(v___x_1868_, 3);
lean_ctor_set(v___x_1868_, 2, v___x_1881_);
lean_ctor_set(v___x_1868_, 1, v___x_1878_);
lean_ctor_set(v___x_1868_, 0, v___x_1877_);
v___x_1883_ = v___x_1868_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 3, v___x_1883_);
lean_ctor_set(v___x_1855_, 2, v___x_1876_);
lean_ctor_set(v___x_1855_, 1, v_binderName_1875_);
lean_ctor_set(v___x_1855_, 0, v_fvarId_1874_);
v___x_1885_ = v___x_1855_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_fvarId_1874_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_binderName_1875_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1886_; lean_object* v_lctx_1887_; lean_object* v_nextIdx_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1907_; 
v___x_1886_ = lean_st_ref_take(v_a_1848_);
v_lctx_1887_ = lean_ctor_get(v___x_1886_, 0);
v_nextIdx_1888_ = lean_ctor_get(v___x_1886_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_1907_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_nextIdx_1888_);
lean_inc(v_lctx_1887_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1907_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v___x_1894_; 
lean_inc_ref(v___x_1885_);
v___x_1892_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1870_, v_lctx_1887_, v___x_1885_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1892_);
v___x_1894_ = v___x_1890_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_nextIdx_1888_);
v___x_1894_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_st_ref_put(v_a_1848_, v___x_1894_);
v___x_1896_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1866_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1905_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1899_ = v___x_1896_;
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1896_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1905_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1885_);
lean_ctor_set(v___x_1901_, 1, v_a_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
else
{
lean_dec_ref(v___x_1885_);
return v___x_1896_;
}
}
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_del_object(v___x_1868_);
lean_dec_ref(v_code_1866_);
lean_dec_ref(v_params_1865_);
lean_del_object(v___x_1855_);
lean_dec(v_discr_1852_);
v_a_1910_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1872_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1872_);
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
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec(v___x_1864_);
lean_del_object(v___x_1855_);
lean_dec(v_discr_1852_);
v___x_1920_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_1921_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1920_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1921_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1926_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1927_ = lean_unsigned_to_nat(2u);
v___x_1928_ = lean_unsigned_to_nat(271u);
v___x_1929_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1930_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1931_ = l_mkPanicMessageWithDecl(v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_, v___x_1926_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_box(0);
v___x_1939_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_1940_ = l_Lean_Expr_const___override(v___x_1939_, v___x_1938_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1941_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1942_ = lean_unsigned_to_nat(34u);
v___x_1943_ = lean_unsigned_to_nat(272u);
v___x_1944_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1945_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1946_ = l_mkPanicMessageWithDecl(v___x_1945_, v___x_1944_, v___x_1943_, v___x_1942_, v___x_1941_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v_discr_1954_; lean_object* v_alts_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_discr_1954_ = lean_ctor_get(v_c_1947_, 2);
v_alts_1955_ = lean_ctor_get(v_c_1947_, 3);
v___x_1956_ = lean_array_get_size(v_alts_1955_);
v___x_1957_ = lean_unsigned_to_nat(1u);
v___x_1958_ = lean_nat_dec_eq(v___x_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_1960_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1959_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_array_get(v___x_1961_, v_alts_1955_, v___x_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_params_1964_; lean_object* v_code_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2063_; 
v_params_1964_ = lean_ctor_get(v___x_1963_, 1);
v_code_1965_ = lean_ctor_get(v___x_1963_, 2);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_1963_, 0);
lean_dec(v_unused_2064_);
v___x_1967_ = v___x_1963_;
v_isShared_1968_ = v_isSharedCheck_2063_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_code_1965_);
lean_inc(v_params_1964_);
lean_dec(v___x_1963_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2063_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = 0;
v___x_1970_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1971_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1969_, v_params_1964_, v_a_1950_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
lean_dec_ref_known(v___x_1971_, 1);
v___x_1972_ = lean_array_get(v___x_1970_, v_params_1964_, v___x_1962_);
lean_dec_ref(v_params_1964_);
v___x_1973_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_1974_ = lean_box(0);
lean_inc(v_discr_1954_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_discr_1954_);
v___x_1976_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1977_ = lean_array_push(v___x_1976_, v___x_1975_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set_tag(v___x_1967_, 3);
lean_ctor_set(v___x_1967_, 2, v___x_1977_);
lean_ctor_set(v___x_1967_, 1, v___x_1974_);
lean_ctor_set(v___x_1967_, 0, v___x_1973_);
v___x_1979_ = v___x_1967_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_2054_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_1981_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_1980_, v_a_1950_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1984_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1969_, v_a_1982_, v___x_1983_, v___x_1979_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_1987_ = 0;
v___x_1988_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_1969_, v___x_1986_, v___x_1987_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_mkArrow(v___x_1986_, v___x_1983_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_fvarId_1992_; lean_object* v_binderName_1993_; lean_object* v_fvarId_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v_lctx_2001_; lean_object* v_nextIdx_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2021_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
v_fvarId_1992_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_fvarId_1992_);
v_binderName_1993_ = lean_ctor_get(v___x_1972_, 1);
lean_inc(v_binderName_1993_);
lean_dec(v___x_1972_);
v_fvarId_1994_ = lean_ctor_get(v_a_1985_, 0);
v___x_1995_ = lean_mk_empty_array_with_capacity(v___x_1957_);
v___x_1996_ = lean_array_push(v___x_1995_, v_a_1989_);
lean_inc(v_fvarId_1994_);
v___x_1997_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_fvarId_1994_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_a_1985_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1999_, 0, v_fvarId_1992_);
lean_ctor_set(v___x_1999_, 1, v_binderName_1993_);
lean_ctor_set(v___x_1999_, 2, v___x_1996_);
lean_ctor_set(v___x_1999_, 3, v_a_1991_);
lean_ctor_set(v___x_1999_, 4, v___x_1998_);
v___x_2000_ = lean_st_ref_take(v_a_1950_);
v_lctx_2001_ = lean_ctor_get(v___x_2000_, 0);
v_nextIdx_2002_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2021_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_nextIdx_2002_);
lean_inc(v_lctx_2001_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2021_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_inc_ref(v___x_1999_);
v___x_2006_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_1969_, v_lctx_2001_, v___x_1999_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2006_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_nextIdx_2002_);
v___x_2008_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = lean_st_ref_put(v_a_1950_, v___x_2008_);
v___x_2010_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1965_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_1999_);
lean_ctor_set(v___x_2015_, 1, v_a_2011_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2015_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
lean_dec_ref_known(v___x_1999_, 5);
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_1989_);
lean_dec(v_a_1985_);
lean_dec(v___x_1972_);
lean_dec_ref(v_code_1965_);
v_a_2022_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1990_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1990_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_1985_);
lean_dec(v___x_1972_);
lean_dec_ref(v_code_1965_);
v_a_2030_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1988_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1988_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v___x_1972_);
lean_dec_ref(v_code_1965_);
v_a_2038_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1984_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1984_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec_ref(v___x_1979_);
lean_dec(v___x_1972_);
lean_dec_ref(v_code_1965_);
v_a_2046_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1981_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1981_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_del_object(v___x_1967_);
lean_dec_ref(v_code_1965_);
lean_dec_ref(v_params_1964_);
v_a_2055_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_1971_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_1971_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v___x_1963_);
v___x_2065_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2066_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2065_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
return v___x_2066_;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2068_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2069_ = lean_unsigned_to_nat(2u);
v___x_2070_ = lean_unsigned_to_nat(260u);
v___x_2071_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2072_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2073_ = l_mkPanicMessageWithDecl(v___x_2072_, v___x_2071_, v___x_2070_, v___x_2069_, v___x_2068_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2078_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2079_ = lean_unsigned_to_nat(34u);
v___x_2080_ = lean_unsigned_to_nat(261u);
v___x_2081_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2082_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2083_ = l_mkPanicMessageWithDecl(v___x_2082_, v___x_2081_, v___x_2080_, v___x_2079_, v___x_2078_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_discr_2091_; lean_object* v_alts_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2161_; 
v_discr_2091_ = lean_ctor_get(v_c_2084_, 2);
v_alts_2092_ = lean_ctor_get(v_c_2084_, 3);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_c_2084_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2162_ = lean_ctor_get(v_c_2084_, 1);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_c_2084_, 0);
lean_dec(v_unused_2163_);
v___x_2094_ = v_c_2084_;
v_isShared_2095_ = v_isSharedCheck_2161_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_alts_2092_);
lean_inc(v_discr_2091_);
lean_dec(v_c_2084_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2161_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2096_ = lean_array_get_size(v_alts_2092_);
v___x_2097_ = lean_unsigned_to_nat(1u);
v___x_2098_ = lean_nat_dec_eq(v___x_2096_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_del_object(v___x_2094_);
lean_dec_ref(v_alts_2092_);
lean_dec(v_discr_2091_);
v___x_2099_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2100_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2099_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2100_;
}
else
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2102_ = lean_unsigned_to_nat(0u);
v___x_2103_ = lean_array_get(v___x_2101_, v_alts_2092_, v___x_2102_);
lean_dec_ref(v_alts_2092_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_params_2104_; lean_object* v_code_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2157_; 
v_params_2104_ = lean_ctor_get(v___x_2103_, 1);
v_code_2105_ = lean_ctor_get(v___x_2103_, 2);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v___x_2103_, 0);
lean_dec(v_unused_2158_);
v___x_2107_ = v___x_2103_;
v_isShared_2108_ = v_isSharedCheck_2157_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_code_2105_);
lean_inc(v_params_2104_);
lean_dec(v___x_2103_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2157_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = 0;
v___x_2110_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2111_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2109_, v_params_2104_, v_a_2087_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; lean_object* v_fvarId_2113_; lean_object* v_binderName_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec_ref_known(v___x_2111_, 1);
v___x_2112_ = lean_array_get(v___x_2110_, v_params_2104_, v___x_2102_);
lean_dec_ref(v_params_2104_);
v_fvarId_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_fvarId_2113_);
v_binderName_2114_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_binderName_2114_);
lean_dec(v___x_2112_);
v___x_2115_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2116_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2117_ = lean_box(0);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_discr_2091_);
v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2097_);
v___x_2120_ = lean_array_push(v___x_2119_, v___x_2118_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set_tag(v___x_2107_, 3);
lean_ctor_set(v___x_2107_, 2, v___x_2120_);
lean_ctor_set(v___x_2107_, 1, v___x_2117_);
lean_ctor_set(v___x_2107_, 0, v___x_2116_);
v___x_2122_ = v___x_2107_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 3, v___x_2122_);
lean_ctor_set(v___x_2094_, 2, v___x_2115_);
lean_ctor_set(v___x_2094_, 1, v_binderName_2114_);
lean_ctor_set(v___x_2094_, 0, v_fvarId_2113_);
v___x_2124_ = v___x_2094_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_fvarId_2113_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v_binderName_2114_);
lean_ctor_set(v_reuseFailAlloc_2147_, 2, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2147_, 3, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v_lctx_2126_; lean_object* v_nextIdx_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2146_; 
v___x_2125_ = lean_st_ref_take(v_a_2087_);
v_lctx_2126_ = lean_ctor_get(v___x_2125_, 0);
v_nextIdx_2127_ = lean_ctor_get(v___x_2125_, 1);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2129_ = v___x_2125_;
v_isShared_2130_ = v_isSharedCheck_2146_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_nextIdx_2127_);
lean_inc(v_lctx_2126_);
lean_dec(v___x_2125_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2146_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2133_; 
lean_inc_ref(v___x_2124_);
v___x_2131_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2109_, v_lctx_2126_, v___x_2124_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2131_);
v___x_2133_ = v___x_2129_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2131_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_nextIdx_2127_);
v___x_2133_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_st_ref_put(v_a_2087_, v___x_2133_);
v___x_2135_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2105_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2124_);
lean_ctor_set(v___x_2140_, 1, v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_dec_ref(v___x_2124_);
return v___x_2135_;
}
}
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_del_object(v___x_2107_);
lean_dec_ref(v_code_2105_);
lean_dec_ref(v_params_2104_);
lean_del_object(v___x_2094_);
lean_dec(v_discr_2091_);
v_a_2149_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2111_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2111_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
lean_dec(v___x_2103_);
lean_del_object(v___x_2094_);
lean_dec(v_discr_2091_);
v___x_2159_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2160_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2159_, v_a_2085_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_);
return v___x_2160_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2165_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2166_ = lean_unsigned_to_nat(2u);
v___x_2167_ = lean_unsigned_to_nat(249u);
v___x_2168_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2169_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2170_ = l_mkPanicMessageWithDecl(v___x_2169_, v___x_2168_, v___x_2167_, v___x_2166_, v___x_2165_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2174_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2175_ = lean_unsigned_to_nat(34u);
v___x_2176_ = lean_unsigned_to_nat(250u);
v___x_2177_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2178_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2179_ = l_mkPanicMessageWithDecl(v___x_2178_, v___x_2177_, v___x_2176_, v___x_2175_, v___x_2174_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_discr_2187_; lean_object* v_alts_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2257_; 
v_discr_2187_ = lean_ctor_get(v_c_2180_, 2);
v_alts_2188_ = lean_ctor_get(v_c_2180_, 3);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_c_2180_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; lean_object* v_unused_2259_; 
v_unused_2258_ = lean_ctor_get(v_c_2180_, 1);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_c_2180_, 0);
lean_dec(v_unused_2259_);
v___x_2190_ = v_c_2180_;
v_isShared_2191_ = v_isSharedCheck_2257_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_alts_2188_);
lean_inc(v_discr_2187_);
lean_dec(v_c_2180_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2257_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2192_ = lean_array_get_size(v_alts_2188_);
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = lean_nat_dec_eq(v___x_2192_, v___x_2193_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_del_object(v___x_2190_);
lean_dec_ref(v_alts_2188_);
lean_dec(v_discr_2187_);
v___x_2195_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2196_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2195_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_array_get(v___x_2197_, v_alts_2188_, v___x_2198_);
lean_dec_ref(v_alts_2188_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_params_2200_; lean_object* v_code_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2253_; 
v_params_2200_ = lean_ctor_get(v___x_2199_, 1);
v_code_2201_ = lean_ctor_get(v___x_2199_, 2);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v___x_2199_, 0);
lean_dec(v_unused_2254_);
v___x_2203_ = v___x_2199_;
v_isShared_2204_ = v_isSharedCheck_2253_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_code_2201_);
lean_inc(v_params_2200_);
lean_dec(v___x_2199_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2253_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = 0;
v___x_2206_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2207_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2205_, v_params_2200_, v_a_2183_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v___x_2208_; lean_object* v_fvarId_2209_; lean_object* v_binderName_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2207_, 1);
v___x_2208_ = lean_array_get(v___x_2206_, v_params_2200_, v___x_2198_);
lean_dec_ref(v_params_2200_);
v_fvarId_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_fvarId_2209_);
v_binderName_2210_ = lean_ctor_get(v___x_2208_, 1);
lean_inc(v_binderName_2210_);
lean_dec(v___x_2208_);
v___x_2211_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2212_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2213_ = lean_box(0);
v___x_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_discr_2187_);
v___x_2215_ = lean_mk_empty_array_with_capacity(v___x_2193_);
v___x_2216_ = lean_array_push(v___x_2215_, v___x_2214_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set_tag(v___x_2203_, 3);
lean_ctor_set(v___x_2203_, 2, v___x_2216_);
lean_ctor_set(v___x_2203_, 1, v___x_2213_);
lean_ctor_set(v___x_2203_, 0, v___x_2212_);
v___x_2218_ = v___x_2203_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2244_, 2, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2220_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 3, v___x_2218_);
lean_ctor_set(v___x_2190_, 2, v___x_2211_);
lean_ctor_set(v___x_2190_, 1, v_binderName_2210_);
lean_ctor_set(v___x_2190_, 0, v_fvarId_2209_);
v___x_2220_ = v___x_2190_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_fvarId_2209_);
lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_binderName_2210_);
lean_ctor_set(v_reuseFailAlloc_2243_, 2, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2243_, 3, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v_lctx_2222_; lean_object* v_nextIdx_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2242_; 
v___x_2221_ = lean_st_ref_take(v_a_2183_);
v_lctx_2222_ = lean_ctor_get(v___x_2221_, 0);
v_nextIdx_2223_ = lean_ctor_get(v___x_2221_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2225_ = v___x_2221_;
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_nextIdx_2223_);
lean_inc(v_lctx_2222_);
lean_dec(v___x_2221_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
lean_inc_ref(v___x_2220_);
v___x_2227_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2205_, v_lctx_2222_, v___x_2220_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_nextIdx_2223_);
v___x_2229_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_st_ref_put(v_a_2183_, v___x_2229_);
v___x_2231_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2201_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2240_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2240_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2240_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2236_; lean_object* v___x_2238_; 
v___x_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2220_);
lean_ctor_set(v___x_2236_, 1, v_a_2232_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2236_);
v___x_2238_ = v___x_2234_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
lean_dec_ref(v___x_2220_);
return v___x_2231_;
}
}
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_del_object(v___x_2203_);
lean_dec_ref(v_code_2201_);
lean_dec_ref(v_params_2200_);
lean_del_object(v___x_2190_);
lean_dec(v_discr_2187_);
v_a_2245_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2207_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2207_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v___x_2199_);
lean_del_object(v___x_2190_);
lean_dec(v_discr_2187_);
v___x_2255_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2256_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2255_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2256_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2261_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2262_ = lean_unsigned_to_nat(2u);
v___x_2263_ = lean_unsigned_to_nat(238u);
v___x_2264_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2265_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2266_ = l_mkPanicMessageWithDecl(v___x_2265_, v___x_2264_, v___x_2263_, v___x_2262_, v___x_2261_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2271_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2272_ = lean_unsigned_to_nat(34u);
v___x_2273_ = lean_unsigned_to_nat(239u);
v___x_2274_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2275_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2276_ = l_mkPanicMessageWithDecl(v___x_2275_, v___x_2274_, v___x_2273_, v___x_2272_, v___x_2271_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_discr_2284_; lean_object* v_alts_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2354_; 
v_discr_2284_ = lean_ctor_get(v_c_2277_, 2);
v_alts_2285_ = lean_ctor_get(v_c_2277_, 3);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_c_2277_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; lean_object* v_unused_2356_; 
v_unused_2355_ = lean_ctor_get(v_c_2277_, 1);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_c_2277_, 0);
lean_dec(v_unused_2356_);
v___x_2287_ = v_c_2277_;
v_isShared_2288_ = v_isSharedCheck_2354_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_alts_2285_);
lean_inc(v_discr_2284_);
lean_dec(v_c_2277_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2354_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = lean_array_get_size(v_alts_2285_);
v___x_2290_ = lean_unsigned_to_nat(1u);
v___x_2291_ = lean_nat_dec_eq(v___x_2289_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_del_object(v___x_2287_);
lean_dec_ref(v_alts_2285_);
lean_dec(v_discr_2284_);
v___x_2292_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2293_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2292_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_array_get(v___x_2294_, v_alts_2285_, v___x_2295_);
lean_dec_ref(v_alts_2285_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_params_2297_; lean_object* v_code_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2350_; 
v_params_2297_ = lean_ctor_get(v___x_2296_, 1);
v_code_2298_ = lean_ctor_get(v___x_2296_, 2);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v___x_2296_, 0);
lean_dec(v_unused_2351_);
v___x_2300_ = v___x_2296_;
v_isShared_2301_ = v_isSharedCheck_2350_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_code_2298_);
lean_inc(v_params_2297_);
lean_dec(v___x_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2350_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = 0;
v___x_2303_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2304_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2302_, v_params_2297_, v_a_2280_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; lean_object* v_fvarId_2306_; lean_object* v_binderName_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_dec_ref_known(v___x_2304_, 1);
v___x_2305_ = lean_array_get(v___x_2303_, v_params_2297_, v___x_2295_);
lean_dec_ref(v_params_2297_);
v_fvarId_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_fvarId_2306_);
v_binderName_2307_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_binderName_2307_);
lean_dec(v___x_2305_);
v___x_2308_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2309_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2311_, 0, v_discr_2284_);
v___x_2312_ = lean_mk_empty_array_with_capacity(v___x_2290_);
v___x_2313_ = lean_array_push(v___x_2312_, v___x_2311_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 3);
lean_ctor_set(v___x_2300_, 2, v___x_2313_);
lean_ctor_set(v___x_2300_, 1, v___x_2310_);
lean_ctor_set(v___x_2300_, 0, v___x_2309_);
v___x_2315_ = v___x_2300_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2317_; 
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 3, v___x_2315_);
lean_ctor_set(v___x_2287_, 2, v___x_2308_);
lean_ctor_set(v___x_2287_, 1, v_binderName_2307_);
lean_ctor_set(v___x_2287_, 0, v_fvarId_2306_);
v___x_2317_ = v___x_2287_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_fvarId_2306_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_binderName_2307_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v___x_2308_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2318_; lean_object* v_lctx_2319_; lean_object* v_nextIdx_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2339_; 
v___x_2318_ = lean_st_ref_take(v_a_2280_);
v_lctx_2319_ = lean_ctor_get(v___x_2318_, 0);
v_nextIdx_2320_ = lean_ctor_get(v___x_2318_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2322_ = v___x_2318_;
v_isShared_2323_ = v_isSharedCheck_2339_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_nextIdx_2320_);
lean_inc(v_lctx_2319_);
lean_dec(v___x_2318_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2339_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
lean_inc_ref(v___x_2317_);
v___x_2324_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2302_, v_lctx_2319_, v___x_2317_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2324_);
v___x_2326_ = v___x_2322_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_nextIdx_2320_);
v___x_2326_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_st_ref_put(v_a_2280_, v___x_2326_);
v___x_2328_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2298_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2337_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2331_ = v___x_2328_;
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2328_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2337_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2317_);
lean_ctor_set(v___x_2333_, 1, v_a_2329_);
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 0, v___x_2333_);
v___x_2335_ = v___x_2331_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
else
{
lean_dec_ref(v___x_2317_);
return v___x_2328_;
}
}
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
lean_del_object(v___x_2300_);
lean_dec_ref(v_code_2298_);
lean_dec_ref(v_params_2297_);
lean_del_object(v___x_2287_);
lean_dec(v_discr_2284_);
v_a_2342_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2304_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2304_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v___x_2296_);
lean_del_object(v___x_2287_);
lean_dec(v_discr_2284_);
v___x_2352_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2353_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2352_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_);
return v___x_2353_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2359_ = lean_unsigned_to_nat(2u);
v___x_2360_ = lean_unsigned_to_nat(227u);
v___x_2361_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2362_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2363_ = l_mkPanicMessageWithDecl(v___x_2362_, v___x_2361_, v___x_2360_, v___x_2359_, v___x_2358_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2368_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2369_ = lean_unsigned_to_nat(34u);
v___x_2370_ = lean_unsigned_to_nat(228u);
v___x_2371_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2372_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2373_ = l_mkPanicMessageWithDecl(v___x_2372_, v___x_2371_, v___x_2370_, v___x_2369_, v___x_2368_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_discr_2381_; lean_object* v_alts_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2451_; 
v_discr_2381_ = lean_ctor_get(v_c_2374_, 2);
v_alts_2382_ = lean_ctor_get(v_c_2374_, 3);
v_isSharedCheck_2451_ = !lean_is_exclusive(v_c_2374_);
if (v_isSharedCheck_2451_ == 0)
{
lean_object* v_unused_2452_; lean_object* v_unused_2453_; 
v_unused_2452_ = lean_ctor_get(v_c_2374_, 1);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v_c_2374_, 0);
lean_dec(v_unused_2453_);
v___x_2384_ = v_c_2374_;
v_isShared_2385_ = v_isSharedCheck_2451_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_alts_2382_);
lean_inc(v_discr_2381_);
lean_dec(v_c_2374_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2451_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2386_ = lean_array_get_size(v_alts_2382_);
v___x_2387_ = lean_unsigned_to_nat(1u);
v___x_2388_ = lean_nat_dec_eq(v___x_2386_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
lean_del_object(v___x_2384_);
lean_dec_ref(v_alts_2382_);
lean_dec(v_discr_2381_);
v___x_2389_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2390_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2389_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
return v___x_2390_;
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = lean_array_get(v___x_2391_, v_alts_2382_, v___x_2392_);
lean_dec_ref(v_alts_2382_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_params_2394_; lean_object* v_code_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2447_; 
v_params_2394_ = lean_ctor_get(v___x_2393_, 1);
v_code_2395_ = lean_ctor_get(v___x_2393_, 2);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v___x_2393_, 0);
lean_dec(v_unused_2448_);
v___x_2397_ = v___x_2393_;
v_isShared_2398_ = v_isSharedCheck_2447_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_code_2395_);
lean_inc(v_params_2394_);
lean_dec(v___x_2393_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2447_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = 0;
v___x_2400_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2401_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2399_, v_params_2394_, v_a_2377_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; lean_object* v_fvarId_2403_; lean_object* v_binderName_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
lean_dec_ref_known(v___x_2401_, 1);
v___x_2402_ = lean_array_get(v___x_2400_, v_params_2394_, v___x_2392_);
lean_dec_ref(v_params_2394_);
v_fvarId_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_fvarId_2403_);
v_binderName_2404_ = lean_ctor_get(v___x_2402_, 1);
lean_inc(v_binderName_2404_);
lean_dec(v___x_2402_);
v___x_2405_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2406_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2407_ = lean_box(0);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v_discr_2381_);
v___x_2409_ = lean_mk_empty_array_with_capacity(v___x_2387_);
v___x_2410_ = lean_array_push(v___x_2409_, v___x_2408_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set_tag(v___x_2397_, 3);
lean_ctor_set(v___x_2397_, 2, v___x_2410_);
lean_ctor_set(v___x_2397_, 1, v___x_2407_);
lean_ctor_set(v___x_2397_, 0, v___x_2406_);
v___x_2412_ = v___x_2397_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2414_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 3, v___x_2412_);
lean_ctor_set(v___x_2384_, 2, v___x_2405_);
lean_ctor_set(v___x_2384_, 1, v_binderName_2404_);
lean_ctor_set(v___x_2384_, 0, v_fvarId_2403_);
v___x_2414_ = v___x_2384_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_fvarId_2403_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_binderName_2404_);
lean_ctor_set(v_reuseFailAlloc_2437_, 2, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2437_, 3, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v_lctx_2416_; lean_object* v_nextIdx_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2436_; 
v___x_2415_ = lean_st_ref_take(v_a_2377_);
v_lctx_2416_ = lean_ctor_get(v___x_2415_, 0);
v_nextIdx_2417_ = lean_ctor_get(v___x_2415_, 1);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2436_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_nextIdx_2417_);
lean_inc(v_lctx_2416_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2436_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
lean_inc_ref(v___x_2414_);
v___x_2421_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2399_, v_lctx_2416_, v___x_2414_);
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 0, v___x_2421_);
v___x_2423_ = v___x_2419_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2421_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_nextIdx_2417_);
v___x_2423_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_st_ref_put(v_a_2377_, v___x_2423_);
v___x_2425_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2395_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2434_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2414_);
lean_ctor_set(v___x_2430_, 1, v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2430_);
v___x_2432_ = v___x_2428_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_dec_ref(v___x_2414_);
return v___x_2425_;
}
}
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_del_object(v___x_2397_);
lean_dec_ref(v_code_2395_);
lean_dec_ref(v_params_2394_);
lean_del_object(v___x_2384_);
lean_dec(v_discr_2381_);
v_a_2439_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2401_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2401_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
lean_dec(v___x_2393_);
lean_del_object(v___x_2384_);
lean_dec(v_discr_2381_);
v___x_2449_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2450_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2449_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
return v___x_2450_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2455_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2456_ = lean_unsigned_to_nat(2u);
v___x_2457_ = lean_unsigned_to_nat(215u);
v___x_2458_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2459_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2460_ = l_mkPanicMessageWithDecl(v___x_2459_, v___x_2458_, v___x_2457_, v___x_2456_, v___x_2455_);
return v___x_2460_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2464_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2465_ = lean_unsigned_to_nat(34u);
v___x_2466_ = lean_unsigned_to_nat(216u);
v___x_2467_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2468_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2469_ = l_mkPanicMessageWithDecl(v___x_2468_, v___x_2467_, v___x_2466_, v___x_2465_, v___x_2464_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_discr_2477_; lean_object* v_alts_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2547_; 
v_discr_2477_ = lean_ctor_get(v_c_2470_, 2);
v_alts_2478_ = lean_ctor_get(v_c_2470_, 3);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_c_2470_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; lean_object* v_unused_2549_; 
v_unused_2548_ = lean_ctor_get(v_c_2470_, 1);
lean_dec(v_unused_2548_);
v_unused_2549_ = lean_ctor_get(v_c_2470_, 0);
lean_dec(v_unused_2549_);
v___x_2480_ = v_c_2470_;
v_isShared_2481_ = v_isSharedCheck_2547_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_alts_2478_);
lean_inc(v_discr_2477_);
lean_dec(v_c_2470_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2547_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2482_ = lean_array_get_size(v_alts_2478_);
v___x_2483_ = lean_unsigned_to_nat(1u);
v___x_2484_ = lean_nat_dec_eq(v___x_2482_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_del_object(v___x_2480_);
lean_dec_ref(v_alts_2478_);
lean_dec(v_discr_2477_);
v___x_2485_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2486_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2485_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2486_;
}
else
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = lean_array_get(v___x_2487_, v_alts_2478_, v___x_2488_);
lean_dec_ref(v_alts_2478_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_params_2490_; lean_object* v_code_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2543_; 
v_params_2490_ = lean_ctor_get(v___x_2489_, 1);
v_code_2491_ = lean_ctor_get(v___x_2489_, 2);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2489_, 0);
lean_dec(v_unused_2544_);
v___x_2493_ = v___x_2489_;
v_isShared_2494_ = v_isSharedCheck_2543_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_code_2491_);
lean_inc(v_params_2490_);
lean_dec(v___x_2489_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2543_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = 0;
v___x_2496_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2497_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2495_, v_params_2490_, v_a_2473_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; lean_object* v_fvarId_2499_; lean_object* v_binderName_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
lean_dec_ref_known(v___x_2497_, 1);
v___x_2498_ = lean_array_get(v___x_2496_, v_params_2490_, v___x_2488_);
lean_dec_ref(v_params_2490_);
v_fvarId_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_fvarId_2499_);
v_binderName_2500_ = lean_ctor_get(v___x_2498_, 1);
lean_inc(v_binderName_2500_);
lean_dec(v___x_2498_);
v___x_2501_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2502_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_discr_2477_);
v___x_2505_ = lean_mk_empty_array_with_capacity(v___x_2483_);
v___x_2506_ = lean_array_push(v___x_2505_, v___x_2504_);
if (v_isShared_2494_ == 0)
{
lean_ctor_set_tag(v___x_2493_, 3);
lean_ctor_set(v___x_2493_, 2, v___x_2506_);
lean_ctor_set(v___x_2493_, 1, v___x_2503_);
lean_ctor_set(v___x_2493_, 0, v___x_2502_);
v___x_2508_ = v___x_2493_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2502_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 3, v___x_2508_);
lean_ctor_set(v___x_2480_, 2, v___x_2501_);
lean_ctor_set(v___x_2480_, 1, v_binderName_2500_);
lean_ctor_set(v___x_2480_, 0, v_fvarId_2499_);
v___x_2510_ = v___x_2480_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fvarId_2499_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_binderName_2500_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2511_; lean_object* v_lctx_2512_; lean_object* v_nextIdx_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2532_; 
v___x_2511_ = lean_st_ref_take(v_a_2473_);
v_lctx_2512_ = lean_ctor_get(v___x_2511_, 0);
v_nextIdx_2513_ = lean_ctor_get(v___x_2511_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2515_ = v___x_2511_;
v_isShared_2516_ = v_isSharedCheck_2532_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_nextIdx_2513_);
lean_inc(v_lctx_2512_);
lean_dec(v___x_2511_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2532_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_inc_ref(v___x_2510_);
v___x_2517_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2495_, v_lctx_2512_, v___x_2510_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2517_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_nextIdx_2513_);
v___x_2519_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_st_ref_put(v_a_2473_, v___x_2519_);
v___x_2521_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2491_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2521_) == 0)
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2530_; 
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2530_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2530_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2510_);
lean_ctor_set(v___x_2526_, 1, v_a_2522_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_dec_ref(v___x_2510_);
return v___x_2521_;
}
}
}
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_del_object(v___x_2493_);
lean_dec_ref(v_code_2491_);
lean_dec_ref(v_params_2490_);
lean_del_object(v___x_2480_);
lean_dec(v_discr_2477_);
v_a_2535_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2497_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2497_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v___x_2489_);
lean_del_object(v___x_2480_);
lean_dec(v_discr_2477_);
v___x_2545_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2546_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2545_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
return v___x_2546_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2551_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2552_ = lean_unsigned_to_nat(2u);
v___x_2553_ = lean_unsigned_to_nat(203u);
v___x_2554_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2555_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2556_ = l_mkPanicMessageWithDecl(v___x_2555_, v___x_2554_, v___x_2553_, v___x_2552_, v___x_2551_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2561_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2562_ = lean_unsigned_to_nat(34u);
v___x_2563_ = lean_unsigned_to_nat(204u);
v___x_2564_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2565_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2566_ = l_mkPanicMessageWithDecl(v___x_2565_, v___x_2564_, v___x_2563_, v___x_2562_, v___x_2561_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_discr_2574_; lean_object* v_alts_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2644_; 
v_discr_2574_ = lean_ctor_get(v_c_2567_, 2);
v_alts_2575_ = lean_ctor_get(v_c_2567_, 3);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_c_2567_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; lean_object* v_unused_2646_; 
v_unused_2645_ = lean_ctor_get(v_c_2567_, 1);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_c_2567_, 0);
lean_dec(v_unused_2646_);
v___x_2577_ = v_c_2567_;
v_isShared_2578_ = v_isSharedCheck_2644_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_alts_2575_);
lean_inc(v_discr_2574_);
lean_dec(v_c_2567_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2644_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2579_ = lean_array_get_size(v_alts_2575_);
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_nat_dec_eq(v___x_2579_, v___x_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
lean_del_object(v___x_2577_);
lean_dec_ref(v_alts_2575_);
lean_dec(v_discr_2574_);
v___x_2582_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2583_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2582_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2583_;
}
else
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_array_get(v___x_2584_, v_alts_2575_, v___x_2585_);
lean_dec_ref(v_alts_2575_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_params_2587_; lean_object* v_code_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2640_; 
v_params_2587_ = lean_ctor_get(v___x_2586_, 1);
v_code_2588_ = lean_ctor_get(v___x_2586_, 2);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2640_ == 0)
{
lean_object* v_unused_2641_; 
v_unused_2641_ = lean_ctor_get(v___x_2586_, 0);
lean_dec(v_unused_2641_);
v___x_2590_ = v___x_2586_;
v_isShared_2591_ = v_isSharedCheck_2640_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_code_2588_);
lean_inc(v_params_2587_);
lean_dec(v___x_2586_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2640_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
uint8_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = 0;
v___x_2593_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2594_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2592_, v_params_2587_, v_a_2570_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v___x_2595_; lean_object* v_fvarId_2596_; lean_object* v_binderName_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec_ref_known(v___x_2594_, 1);
v___x_2595_ = lean_array_get(v___x_2593_, v_params_2587_, v___x_2585_);
lean_dec_ref(v_params_2587_);
v_fvarId_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_fvarId_2596_);
v_binderName_2597_ = lean_ctor_get(v___x_2595_, 1);
lean_inc(v_binderName_2597_);
lean_dec(v___x_2595_);
v___x_2598_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2599_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2600_ = lean_box(0);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_discr_2574_);
v___x_2602_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2603_ = lean_array_push(v___x_2602_, v___x_2601_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 3);
lean_ctor_set(v___x_2590_, 2, v___x_2603_);
lean_ctor_set(v___x_2590_, 1, v___x_2600_);
lean_ctor_set(v___x_2590_, 0, v___x_2599_);
v___x_2605_ = v___x_2590_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 3, v___x_2605_);
lean_ctor_set(v___x_2577_, 2, v___x_2598_);
lean_ctor_set(v___x_2577_, 1, v_binderName_2597_);
lean_ctor_set(v___x_2577_, 0, v_fvarId_2596_);
v___x_2607_ = v___x_2577_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_fvarId_2596_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_binderName_2597_);
lean_ctor_set(v_reuseFailAlloc_2630_, 2, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2630_, 3, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2608_; lean_object* v_lctx_2609_; lean_object* v_nextIdx_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2629_; 
v___x_2608_ = lean_st_ref_take(v_a_2570_);
v_lctx_2609_ = lean_ctor_get(v___x_2608_, 0);
v_nextIdx_2610_ = lean_ctor_get(v___x_2608_, 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2612_ = v___x_2608_;
v_isShared_2613_ = v_isSharedCheck_2629_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_nextIdx_2610_);
lean_inc(v_lctx_2609_);
lean_dec(v___x_2608_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2629_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_inc_ref(v___x_2607_);
v___x_2614_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2592_, v_lctx_2609_, v___x_2607_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v___x_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2614_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_nextIdx_2610_);
v___x_2616_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_st_ref_put(v_a_2570_, v___x_2616_);
v___x_2618_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2588_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2627_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2627_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2607_);
lean_ctor_set(v___x_2623_, 1, v_a_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2625_ = v___x_2621_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
else
{
lean_dec_ref(v___x_2607_);
return v___x_2618_;
}
}
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_del_object(v___x_2590_);
lean_dec_ref(v_code_2588_);
lean_dec_ref(v_params_2587_);
lean_del_object(v___x_2577_);
lean_dec(v_discr_2574_);
v_a_2632_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2594_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2594_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
lean_dec(v___x_2586_);
lean_del_object(v___x_2577_);
lean_dec(v_discr_2574_);
v___x_2642_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_2643_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2642_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2643_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2648_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2649_ = lean_unsigned_to_nat(2u);
v___x_2650_ = lean_unsigned_to_nat(192u);
v___x_2651_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2652_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2653_ = l_mkPanicMessageWithDecl(v___x_2652_, v___x_2651_, v___x_2650_, v___x_2649_, v___x_2648_);
return v___x_2653_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2655_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2656_ = lean_unsigned_to_nat(34u);
v___x_2657_ = lean_unsigned_to_nat(193u);
v___x_2658_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2659_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2660_ = l_mkPanicMessageWithDecl(v___x_2659_, v___x_2658_, v___x_2657_, v___x_2656_, v___x_2655_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_2661_, lean_object* v_uintName_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_){
_start:
{
lean_object* v_discr_2669_; lean_object* v_alts_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2740_; 
v_discr_2669_ = lean_ctor_get(v_c_2661_, 2);
v_alts_2670_ = lean_ctor_get(v_c_2661_, 3);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_c_2661_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2741_ = lean_ctor_get(v_c_2661_, 1);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_c_2661_, 0);
lean_dec(v_unused_2742_);
v___x_2672_ = v_c_2661_;
v_isShared_2673_ = v_isSharedCheck_2740_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_alts_2670_);
lean_inc(v_discr_2669_);
lean_dec(v_c_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2740_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v___x_2674_ = lean_array_get_size(v_alts_2670_);
v___x_2675_ = lean_unsigned_to_nat(1u);
v___x_2676_ = lean_nat_dec_eq(v___x_2674_, v___x_2675_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_del_object(v___x_2672_);
lean_dec_ref(v_alts_2670_);
lean_dec(v_discr_2669_);
lean_dec(v_uintName_2662_);
v___x_2677_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_2678_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2677_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
return v___x_2678_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2679_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0);
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = lean_array_get(v___x_2679_, v_alts_2670_, v___x_2680_);
lean_dec_ref(v_alts_2670_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_params_2682_; lean_object* v_code_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2736_; 
v_params_2682_ = lean_ctor_get(v___x_2681_, 1);
v_code_2683_ = lean_ctor_get(v___x_2681_, 2);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; 
v_unused_2737_ = lean_ctor_get(v___x_2681_, 0);
lean_dec(v_unused_2737_);
v___x_2685_ = v___x_2681_;
v_isShared_2686_ = v_isSharedCheck_2736_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_code_2683_);
lean_inc(v_params_2682_);
lean_dec(v___x_2681_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2736_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = 0;
v___x_2688_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2689_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2687_, v_params_2682_, v_a_2665_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v___x_2690_; lean_object* v_fvarId_2691_; lean_object* v_binderName_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
lean_dec_ref_known(v___x_2689_, 1);
v___x_2690_ = lean_array_get(v___x_2688_, v_params_2682_, v___x_2680_);
lean_dec_ref(v_params_2682_);
v_fvarId_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_fvarId_2691_);
v_binderName_2692_ = lean_ctor_get(v___x_2690_, 1);
lean_inc(v_binderName_2692_);
lean_dec(v___x_2690_);
v___x_2693_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2694_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4));
v___x_2695_ = l_Lean_Name_str___override(v_uintName_2662_, v___x_2694_);
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_discr_2669_);
v___x_2698_ = lean_mk_empty_array_with_capacity(v___x_2675_);
v___x_2699_ = lean_array_push(v___x_2698_, v___x_2697_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set_tag(v___x_2685_, 3);
lean_ctor_set(v___x_2685_, 2, v___x_2699_);
lean_ctor_set(v___x_2685_, 1, v___x_2696_);
lean_ctor_set(v___x_2685_, 0, v___x_2695_);
v___x_2701_ = v___x_2685_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2727_, 2, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2703_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 3, v___x_2701_);
lean_ctor_set(v___x_2672_, 2, v___x_2693_);
lean_ctor_set(v___x_2672_, 1, v_binderName_2692_);
lean_ctor_set(v___x_2672_, 0, v_fvarId_2691_);
v___x_2703_ = v___x_2672_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_fvarId_2691_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_binderName_2692_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; lean_object* v_lctx_2705_; lean_object* v_nextIdx_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2725_; 
v___x_2704_ = lean_st_ref_take(v_a_2665_);
v_lctx_2705_ = lean_ctor_get(v___x_2704_, 0);
v_nextIdx_2706_ = lean_ctor_get(v___x_2704_, 1);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2704_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2708_ = v___x_2704_;
v_isShared_2709_ = v_isSharedCheck_2725_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_nextIdx_2706_);
lean_inc(v_lctx_2705_);
lean_dec(v___x_2704_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2725_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
lean_inc_ref(v___x_2703_);
v___x_2710_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2687_, v_lctx_2705_, v___x_2703_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2710_);
v___x_2712_ = v___x_2708_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_nextIdx_2706_);
v___x_2712_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_st_ref_put(v_a_2665_, v___x_2712_);
v___x_2714_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2683_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2723_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2723_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2703_);
lean_ctor_set(v___x_2719_, 1, v_a_2715_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v___x_2719_);
v___x_2721_ = v___x_2717_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
else
{
lean_dec_ref(v___x_2703_);
return v___x_2714_;
}
}
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_del_object(v___x_2685_);
lean_dec_ref(v_code_2683_);
lean_dec_ref(v_params_2682_);
lean_del_object(v___x_2672_);
lean_dec(v_discr_2669_);
lean_dec(v_uintName_2662_);
v_a_2728_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2689_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2689_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec(v___x_2681_);
lean_del_object(v___x_2672_);
lean_dec(v_discr_2669_);
lean_dec(v_uintName_2662_);
v___x_2738_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5);
v___x_2739_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2738_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_);
return v___x_2739_;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_2745_ = l_Lean_mkConst(v___x_2744_, v___x_2743_);
return v___x_2745_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2752_ = lean_box(0);
v___x_2753_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_2754_ = l_Lean_mkConst(v___x_2753_, v___x_2752_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_2767_ = l_Lean_mkConst(v___x_2766_, v___x_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_2800_, size_t v_sz_2801_, size_t v_i_2802_, lean_object* v_bs_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_usize_dec_lt(v_i_2802_, v_sz_2801_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
lean_dec(v___x_2800_);
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_bs_2803_);
return v___x_2811_;
}
else
{
lean_object* v_v_2812_; lean_object* v___x_2813_; lean_object* v_bs_x27_2814_; lean_object* v_a_2816_; 
v_v_2812_ = lean_array_uget(v_bs_2803_, v_i_2802_);
v___x_2813_ = lean_unsigned_to_nat(0u);
v_bs_x27_2814_ = lean_array_uset(v_bs_2803_, v_i_2802_, v___x_2813_);
if (lean_obj_tag(v_v_2812_) == 0)
{
lean_object* v_ctorName_2821_; lean_object* v_params_2822_; lean_object* v_code_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2950_; 
v_ctorName_2821_ = lean_ctor_get(v_v_2812_, 0);
v_params_2822_ = lean_ctor_get(v_v_2812_, 1);
v_code_2823_ = lean_ctor_get(v_v_2812_, 2);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_v_2812_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2825_ = v_v_2812_;
v_isShared_2826_ = v_isSharedCheck_2950_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_code_2823_);
lean_inc(v_params_2822_);
lean_inc(v_ctorName_2821_);
lean_dec(v_v_2812_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2950_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2827_ = 0;
v___x_2828_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2831_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2827_, v_params_2822_, v___y_2806_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
lean_dec_ref_known(v___x_2831_, 1);
v___x_2832_ = lean_array_get(v___x_2828_, v_params_2822_, v___x_2813_);
lean_dec_ref(v_params_2822_);
v___x_2833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_2834_ = lean_name_eq(v_ctorName_2821_, v___x_2833_);
lean_dec(v_ctorName_2821_);
if (v___x_2834_ == 0)
{
lean_object* v_fvarId_2835_; lean_object* v_binderName_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_lctx_2844_; lean_object* v_nextIdx_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2870_; 
v_fvarId_2835_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_fvarId_2835_);
v_binderName_2836_ = lean_ctor_get(v___x_2832_, 1);
lean_inc(v_binderName_2836_);
lean_dec(v___x_2832_);
v___x_2837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2838_ = lean_unsigned_to_nat(1u);
v___x_2839_ = lean_mk_empty_array_with_capacity(v___x_2838_);
lean_inc(v___x_2800_);
v___x_2840_ = lean_array_push(v___x_2839_, v___x_2800_);
v___x_2841_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2837_);
lean_ctor_set(v___x_2841_, 1, v___x_2829_);
lean_ctor_set(v___x_2841_, 2, v___x_2840_);
v___x_2842_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2842_, 0, v_fvarId_2835_);
lean_ctor_set(v___x_2842_, 1, v_binderName_2836_);
lean_ctor_set(v___x_2842_, 2, v___x_2830_);
lean_ctor_set(v___x_2842_, 3, v___x_2841_);
v___x_2843_ = lean_st_ref_take(v___y_2806_);
v_lctx_2844_ = lean_ctor_get(v___x_2843_, 0);
v_nextIdx_2845_ = lean_ctor_get(v___x_2843_, 1);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2847_ = v___x_2843_;
v_isShared_2848_ = v_isSharedCheck_2870_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_nextIdx_2845_);
lean_inc(v_lctx_2844_);
lean_dec(v___x_2843_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2870_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_inc_ref(v___x_2842_);
v___x_2849_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2827_, v_lctx_2844_, v___x_2842_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_nextIdx_2845_);
v___x_2851_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_st_ref_put(v___y_2806_, v___x_2851_);
v___x_2853_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2823_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_2856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2842_);
lean_ctor_set(v___x_2857_, 1, v_a_2854_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 2, v___x_2857_);
lean_ctor_set(v___x_2825_, 1, v___x_2856_);
lean_ctor_set(v___x_2825_, 0, v___x_2855_);
v___x_2859_ = v___x_2825_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
v_a_2816_ = v___x_2859_;
goto v___jp_2815_;
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref_known(v___x_2842_, 4);
lean_del_object(v___x_2825_);
lean_dec_ref(v_bs_x27_2814_);
lean_dec(v___x_2800_);
v_a_2861_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2853_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2853_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_2872_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2873_ = lean_unsigned_to_nat(1u);
v___x_2874_ = lean_mk_empty_array_with_capacity(v___x_2873_);
lean_inc(v___x_2800_);
v___x_2875_ = lean_array_push(v___x_2874_, v___x_2800_);
v___x_2876_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2872_);
lean_ctor_set(v___x_2876_, 1, v___x_2829_);
lean_ctor_set(v___x_2876_, 2, v___x_2875_);
v___x_2877_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2827_, v___x_2871_, v___x_2830_, v___x_2876_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_2880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_2881_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2827_, v___x_2879_, v___x_2830_, v___x_2880_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v_fvarId_2883_; lean_object* v_binderName_2884_; lean_object* v_fvarId_2885_; lean_object* v_fvarId_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_lctx_2897_; lean_object* v_nextIdx_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2925_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
v_fvarId_2883_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_fvarId_2883_);
v_binderName_2884_ = lean_ctor_get(v___x_2832_, 1);
lean_inc(v_binderName_2884_);
lean_dec(v___x_2832_);
v_fvarId_2885_ = lean_ctor_get(v_a_2878_, 0);
v_fvarId_2886_ = lean_ctor_get(v_a_2882_, 0);
v___x_2887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_2885_);
v___x_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2888_, 0, v_fvarId_2885_);
lean_inc(v_fvarId_2886_);
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_fvarId_2886_);
v___x_2890_ = lean_unsigned_to_nat(2u);
v___x_2891_ = lean_mk_empty_array_with_capacity(v___x_2890_);
v___x_2892_ = lean_array_push(v___x_2891_, v___x_2888_);
v___x_2893_ = lean_array_push(v___x_2892_, v___x_2889_);
v___x_2894_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2887_);
lean_ctor_set(v___x_2894_, 1, v___x_2829_);
lean_ctor_set(v___x_2894_, 2, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2895_, 0, v_fvarId_2883_);
lean_ctor_set(v___x_2895_, 1, v_binderName_2884_);
lean_ctor_set(v___x_2895_, 2, v___x_2830_);
lean_ctor_set(v___x_2895_, 3, v___x_2894_);
v___x_2896_ = lean_st_ref_take(v___y_2806_);
v_lctx_2897_ = lean_ctor_get(v___x_2896_, 0);
v_nextIdx_2898_ = lean_ctor_get(v___x_2896_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2900_ = v___x_2896_;
v_isShared_2901_ = v_isSharedCheck_2925_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_nextIdx_2898_);
lean_inc(v_lctx_2897_);
lean_dec(v___x_2896_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2925_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; lean_object* v___x_2904_; 
lean_inc_ref(v___x_2895_);
v___x_2902_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2827_, v_lctx_2897_, v___x_2895_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v___x_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2902_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_nextIdx_2898_);
v___x_2904_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_st_ref_put(v___y_2806_, v___x_2904_);
v___x_2906_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2823_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 1);
v___x_2908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_2909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2895_);
lean_ctor_set(v___x_2910_, 1, v_a_2907_);
v___x_2911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2911_, 0, v_a_2882_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2878_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 2, v___x_2912_);
lean_ctor_set(v___x_2825_, 1, v___x_2909_);
lean_ctor_set(v___x_2825_, 0, v___x_2908_);
v___x_2914_ = v___x_2825_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
v_a_2816_ = v___x_2914_;
goto v___jp_2815_;
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref_known(v___x_2895_, 4);
lean_dec(v_a_2882_);
lean_dec(v_a_2878_);
lean_del_object(v___x_2825_);
lean_dec_ref(v_bs_x27_2814_);
lean_dec(v___x_2800_);
v_a_2916_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2906_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2906_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_a_2878_);
lean_dec(v___x_2832_);
lean_del_object(v___x_2825_);
lean_dec_ref(v_code_2823_);
lean_dec_ref(v_bs_x27_2814_);
lean_dec(v___x_2800_);
v_a_2926_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2881_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2881_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v___x_2832_);
lean_del_object(v___x_2825_);
lean_dec_ref(v_code_2823_);
lean_dec_ref(v_bs_x27_2814_);
lean_dec(v___x_2800_);
v_a_2934_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2877_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2877_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_del_object(v___x_2825_);
lean_dec_ref(v_code_2823_);
lean_dec_ref(v_params_2822_);
lean_dec(v_ctorName_2821_);
lean_dec_ref(v_bs_x27_2814_);
lean_dec(v___x_2800_);
v_a_2942_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2831_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2831_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
else
{
lean_object* v_code_2951_; lean_object* v___x_2952_; 
v_code_2951_ = lean_ctor_get(v_v_2812_, 0);
lean_inc_ref(v_code_2951_);
v___x_2952_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2951_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2812_, v_a_2953_);
v_a_2816_ = v___x_2954_;
goto v___jp_2815_;
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref_known(v_v_2812_, 1);
lean_dec_ref(v_bs_x27_2814_);
lean_dec(v___x_2800_);
v_a_2955_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2952_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2952_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
v___jp_2815_:
{
size_t v___x_2817_; size_t v___x_2818_; lean_object* v___x_2819_; 
v___x_2817_ = ((size_t)1ULL);
v___x_2818_ = lean_usize_add(v_i_2802_, v___x_2817_);
v___x_2819_ = lean_array_uset(v_bs_x27_2814_, v_i_2802_, v_a_2816_);
v_i_2802_ = v___x_2818_;
v_bs_2803_ = v___x_2819_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_){
_start:
{
lean_object* v_resultType_2970_; lean_object* v_discr_2971_; lean_object* v_alts_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_3069_; 
v_resultType_2970_ = lean_ctor_get(v_c_2963_, 1);
v_discr_2971_ = lean_ctor_get(v_c_2963_, 2);
v_alts_2972_ = lean_ctor_get(v_c_2963_, 3);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_c_2963_);
if (v_isSharedCheck_3069_ == 0)
{
lean_object* v_unused_3070_; 
v_unused_3070_ = lean_ctor_get(v_c_2963_, 0);
lean_dec(v_unused_3070_);
v___x_2974_ = v_c_2963_;
v_isShared_2975_ = v_isSharedCheck_3069_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_alts_2972_);
lean_inc(v_discr_2971_);
lean_inc(v_resultType_2970_);
lean_dec(v_c_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_3069_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
uint8_t v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = 0;
v___x_2977_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_2970_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2981_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_2982_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_2983_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2976_, v___x_2981_, v___x_2980_, v___x_2982_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v_fvarId_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v_fvarId_2985_ = lean_ctor_get(v_a_2984_, 0);
v___x_2986_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_2987_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_2988_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_2985_);
v___x_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2989_, 0, v_fvarId_2985_);
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = lean_mk_empty_array_with_capacity(v___x_2990_);
v___x_2992_ = lean_array_push(v___x_2991_, v___x_2989_);
v___x_2993_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2988_);
lean_ctor_set(v___x_2993_, 1, v___x_2979_);
lean_ctor_set(v___x_2993_, 2, v___x_2992_);
v___x_2994_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2976_, v___x_2986_, v___x_2987_, v___x_2993_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v_fvarId_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v_fvarId_2996_ = lean_ctor_get(v_a_2995_, 0);
v___x_2997_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_2998_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_2999_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3000_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_discr_2971_);
lean_inc(v_fvarId_2996_);
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_fvarId_2996_);
v___x_3003_ = lean_unsigned_to_nat(2u);
v___x_3004_ = lean_mk_empty_array_with_capacity(v___x_3003_);
lean_inc_ref(v___x_3001_);
v___x_3005_ = lean_array_push(v___x_3004_, v___x_3001_);
v___x_3006_ = lean_array_push(v___x_3005_, v___x_3002_);
v___x_3007_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3000_);
lean_ctor_set(v___x_3007_, 1, v___x_2979_);
lean_ctor_set(v___x_3007_, 2, v___x_3006_);
v___x_3008_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2976_, v___x_2997_, v___x_2999_, v___x_3007_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; size_t v_sz_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref_known(v___x_3008_, 1);
v_sz_3010_ = lean_array_size(v_alts_2972_);
v___x_3011_ = ((size_t)0ULL);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3001_, v_sz_3010_, v___x_3011_, v_alts_2972_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3028_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3015_ = v___x_3012_;
v_isShared_3016_ = v_isSharedCheck_3028_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3028_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_fvarId_3017_; lean_object* v___x_3019_; 
v_fvarId_3017_ = lean_ctor_get(v_a_3009_, 0);
lean_inc(v_fvarId_3017_);
if (v_isShared_2975_ == 0)
{
lean_ctor_set(v___x_2974_, 3, v_a_3013_);
lean_ctor_set(v___x_2974_, 2, v_fvarId_3017_);
lean_ctor_set(v___x_2974_, 1, v_a_2978_);
lean_ctor_set(v___x_2974_, 0, v___x_2998_);
v___x_3019_ = v___x_2974_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_a_2978_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_fvarId_3017_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_a_3013_);
v___x_3019_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3020_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3021_, 0, v_a_3009_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v_a_2995_);
lean_ctor_set(v___x_3022_, 1, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_a_2984_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v___x_3023_);
v___x_3025_ = v___x_3015_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_a_3009_);
lean_dec(v_a_2995_);
lean_dec(v_a_2984_);
lean_dec(v_a_2978_);
lean_del_object(v___x_2974_);
v_a_3029_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3012_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3012_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref_known(v___x_3001_, 1);
lean_dec(v_a_2995_);
lean_dec(v_a_2984_);
lean_dec(v_a_2978_);
lean_del_object(v___x_2974_);
lean_dec_ref(v_alts_2972_);
v_a_3037_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3008_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3008_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec(v_a_2984_);
lean_dec(v_a_2978_);
lean_del_object(v___x_2974_);
lean_dec_ref(v_alts_2972_);
lean_dec(v_discr_2971_);
v_a_3045_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_2994_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_2994_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_dec(v_a_2978_);
lean_del_object(v___x_2974_);
lean_dec_ref(v_alts_2972_);
lean_dec(v_discr_2971_);
v_a_3053_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_2983_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_2983_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_del_object(v___x_2974_);
lean_dec_ref(v_alts_2972_);
lean_dec(v_discr_2971_);
v_a_3061_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_2977_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_2977_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3080_, size_t v_sz_3081_, size_t v_i_3082_, lean_object* v_bs_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_usize_dec_lt(v_i_3082_, v_sz_3081_);
if (v___x_3090_ == 0)
{
lean_object* v___x_3091_; 
lean_dec(v___x_3080_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_bs_3083_);
return v___x_3091_;
}
else
{
lean_object* v_v_3092_; lean_object* v___x_3093_; lean_object* v_bs_x27_3094_; lean_object* v_a_3096_; 
v_v_3092_ = lean_array_uget(v_bs_3083_, v_i_3082_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v_bs_x27_3094_ = lean_array_uset(v_bs_3083_, v_i_3082_, v___x_3093_);
if (lean_obj_tag(v_v_3092_) == 0)
{
lean_object* v_ctorName_3101_; lean_object* v_params_3102_; lean_object* v_code_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3190_; 
v_ctorName_3101_ = lean_ctor_get(v_v_3092_, 0);
v_params_3102_ = lean_ctor_get(v_v_3092_, 1);
v_code_3103_ = lean_ctor_get(v_v_3092_, 2);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_v_3092_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3105_ = v_v_3092_;
v_isShared_3106_ = v_isSharedCheck_3190_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_code_3103_);
lean_inc(v_params_3102_);
lean_inc(v_ctorName_3101_);
lean_dec(v_v_3092_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3190_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3107_ = 0;
v___x_3108_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_3109_ = lean_box(0);
v___x_3110_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3111_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3107_, v_params_3102_, v___y_3086_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
lean_dec_ref_known(v___x_3111_, 1);
v___x_3112_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_3113_ = lean_name_eq(v_ctorName_3101_, v___x_3112_);
lean_dec(v_ctorName_3101_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; 
lean_dec_ref(v_params_3102_);
v___x_3114_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3103_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 2, v_a_3115_);
lean_ctor_set(v___x_3105_, 1, v___x_3117_);
lean_ctor_set(v___x_3105_, 0, v___x_3116_);
v___x_3119_ = v___x_3105_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_a_3115_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
v_a_3096_ = v___x_3119_;
goto v___jp_3095_;
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_del_object(v___x_3105_);
lean_dec_ref(v_bs_x27_3094_);
lean_dec(v___x_3080_);
v_a_3121_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3114_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3114_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3129_ = lean_array_get(v___x_3108_, v_params_3102_, v___x_3093_);
lean_dec_ref(v_params_3102_);
v___x_3130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_3131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3132_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3107_, v___x_3130_, v___x_3110_, v___x_3131_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v_fvarId_3134_; lean_object* v_binderName_3135_; lean_object* v_fvarId_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_lctx_3146_; lean_object* v_nextIdx_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3173_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v_fvarId_3134_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_fvarId_3134_);
v_binderName_3135_ = lean_ctor_get(v___x_3129_, 1);
lean_inc(v_binderName_3135_);
lean_dec(v___x_3129_);
v_fvarId_3136_ = lean_ctor_get(v_a_3133_, 0);
v___x_3137_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_3136_);
v___x_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3138_, 0, v_fvarId_3136_);
v___x_3139_ = lean_unsigned_to_nat(2u);
v___x_3140_ = lean_mk_empty_array_with_capacity(v___x_3139_);
lean_inc(v___x_3080_);
v___x_3141_ = lean_array_push(v___x_3140_, v___x_3080_);
v___x_3142_ = lean_array_push(v___x_3141_, v___x_3138_);
v___x_3143_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3137_);
lean_ctor_set(v___x_3143_, 1, v___x_3109_);
lean_ctor_set(v___x_3143_, 2, v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3144_, 0, v_fvarId_3134_);
lean_ctor_set(v___x_3144_, 1, v_binderName_3135_);
lean_ctor_set(v___x_3144_, 2, v___x_3110_);
lean_ctor_set(v___x_3144_, 3, v___x_3143_);
v___x_3145_ = lean_st_ref_take(v___y_3086_);
v_lctx_3146_ = lean_ctor_get(v___x_3145_, 0);
v_nextIdx_3147_ = lean_ctor_get(v___x_3145_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3149_ = v___x_3145_;
v_isShared_3150_ = v_isSharedCheck_3173_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_nextIdx_3147_);
lean_inc(v_lctx_3146_);
lean_dec(v___x_3145_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3173_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_inc_ref(v___x_3144_);
v___x_3151_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3107_, v_lctx_3146_, v___x_3144_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3151_);
v___x_3153_ = v___x_3149_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_nextIdx_3147_);
v___x_3153_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_st_ref_put(v___y_3086_, v___x_3153_);
v___x_3155_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3103_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3155_, 1);
v___x_3157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_3158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3144_);
lean_ctor_set(v___x_3159_, 1, v_a_3156_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_a_3133_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 2, v___x_3160_);
lean_ctor_set(v___x_3105_, 1, v___x_3158_);
lean_ctor_set(v___x_3105_, 0, v___x_3157_);
v___x_3162_ = v___x_3105_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
v_a_3096_ = v___x_3162_;
goto v___jp_3095_;
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref_known(v___x_3144_, 4);
lean_dec(v_a_3133_);
lean_del_object(v___x_3105_);
lean_dec_ref(v_bs_x27_3094_);
lean_dec(v___x_3080_);
v_a_3164_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3155_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3155_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v___x_3129_);
lean_del_object(v___x_3105_);
lean_dec_ref(v_code_3103_);
lean_dec_ref(v_bs_x27_3094_);
lean_dec(v___x_3080_);
v_a_3174_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3132_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3132_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_del_object(v___x_3105_);
lean_dec_ref(v_code_3103_);
lean_dec_ref(v_params_3102_);
lean_dec(v_ctorName_3101_);
lean_dec_ref(v_bs_x27_3094_);
lean_dec(v___x_3080_);
v_a_3182_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3111_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3111_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
else
{
lean_object* v_code_3191_; lean_object* v___x_3192_; 
v_code_3191_ = lean_ctor_get(v_v_3092_, 0);
lean_inc_ref(v_code_3191_);
v___x_3192_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3191_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3194_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3092_, v_a_3193_);
v_a_3096_ = v___x_3194_;
goto v___jp_3095_;
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref_known(v_v_3092_, 1);
lean_dec_ref(v_bs_x27_3094_);
lean_dec(v___x_3080_);
v_a_3195_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3192_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3192_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
v___jp_3095_:
{
size_t v___x_3097_; size_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = ((size_t)1ULL);
v___x_3098_ = lean_usize_add(v_i_3082_, v___x_3097_);
v___x_3099_ = lean_array_uset(v_bs_x27_3094_, v_i_3082_, v_a_3096_);
v_i_3082_ = v___x_3098_;
v_bs_3083_ = v___x_3099_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_){
_start:
{
lean_object* v_resultType_3210_; lean_object* v_discr_3211_; lean_object* v_alts_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3289_; 
v_resultType_3210_ = lean_ctor_get(v_c_3203_, 1);
v_discr_3211_ = lean_ctor_get(v_c_3203_, 2);
v_alts_3212_ = lean_ctor_get(v_c_3203_, 3);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_c_3203_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; 
v_unused_3290_ = lean_ctor_get(v_c_3203_, 0);
lean_dec(v_unused_3290_);
v___x_3214_ = v_c_3203_;
v_isShared_3215_ = v_isSharedCheck_3289_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_alts_3212_);
lean_inc(v_discr_3211_);
lean_inc(v_resultType_3210_);
lean_dec(v_c_3203_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3289_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint8_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = 0;
v___x_3217_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3210_, v_a_3207_, v_a_3208_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = lean_box(0);
v___x_3220_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3221_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3222_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_3223_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3216_, v___x_3221_, v___x_3220_, v___x_3222_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v_fvarId_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v_fvarId_3225_ = lean_ctor_get(v_a_3224_, 0);
v___x_3226_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3227_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3228_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3229_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9));
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v_discr_3211_);
lean_inc(v_fvarId_3225_);
v___x_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3231_, 0, v_fvarId_3225_);
v___x_3232_ = lean_unsigned_to_nat(2u);
v___x_3233_ = lean_mk_empty_array_with_capacity(v___x_3232_);
lean_inc_ref(v___x_3230_);
v___x_3234_ = lean_array_push(v___x_3233_, v___x_3230_);
v___x_3235_ = lean_array_push(v___x_3234_, v___x_3231_);
v___x_3236_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3229_);
lean_ctor_set(v___x_3236_, 1, v___x_3219_);
lean_ctor_set(v___x_3236_, 2, v___x_3235_);
v___x_3237_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3216_, v___x_3226_, v___x_3228_, v___x_3236_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; size_t v_sz_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v_sz_3239_ = lean_array_size(v_alts_3212_);
v___x_3240_ = ((size_t)0ULL);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3230_, v_sz_3239_, v___x_3240_, v_alts_3212_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3256_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3256_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3256_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v_fvarId_3246_; lean_object* v___x_3248_; 
v_fvarId_3246_ = lean_ctor_get(v_a_3238_, 0);
lean_inc(v_fvarId_3246_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 3, v_a_3242_);
lean_ctor_set(v___x_3214_, 2, v_fvarId_3246_);
lean_ctor_set(v___x_3214_, 1, v_a_3218_);
lean_ctor_set(v___x_3214_, 0, v___x_3227_);
v___x_3248_ = v___x_3214_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_a_3218_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v_fvarId_3246_);
lean_ctor_set(v_reuseFailAlloc_3255_, 3, v_a_3242_);
v___x_3248_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3249_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_a_3238_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v_a_3224_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3251_);
v___x_3253_ = v___x_3244_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v_a_3238_);
lean_dec(v_a_3224_);
lean_dec(v_a_3218_);
lean_del_object(v___x_3214_);
v_a_3257_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3241_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3241_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_dec_ref_known(v___x_3230_, 1);
lean_dec(v_a_3224_);
lean_dec(v_a_3218_);
lean_del_object(v___x_3214_);
lean_dec_ref(v_alts_3212_);
v_a_3265_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3237_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3237_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_a_3218_);
lean_del_object(v___x_3214_);
lean_dec_ref(v_alts_3212_);
lean_dec(v_discr_3211_);
v_a_3273_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3223_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3223_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_del_object(v___x_3214_);
lean_dec_ref(v_alts_3212_);
lean_dec(v_discr_3211_);
v_a_3281_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3217_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3217_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v_decl_3307_; lean_object* v_k_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; 
switch(lean_obj_tag(v_code_3291_))
{
case 0:
{
lean_object* v_decl_3415_; lean_object* v_k_3416_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v_value_3472_; 
v_decl_3415_ = lean_ctor_get(v_code_3291_, 0);
v_k_3416_ = lean_ctor_get(v_code_3291_, 1);
v_value_3472_ = lean_ctor_get(v_decl_3415_, 3);
lean_inc(v_value_3472_);
if (lean_obj_tag(v_value_3472_) == 3)
{
lean_object* v_declName_3473_; 
v_declName_3473_ = lean_ctor_get(v_value_3472_, 0);
lean_inc(v_declName_3473_);
if (lean_obj_tag(v_declName_3473_) == 1)
{
lean_object* v_pre_3474_; 
v_pre_3474_ = lean_ctor_get(v_declName_3473_, 0);
lean_inc(v_pre_3474_);
if (lean_obj_tag(v_pre_3474_) == 1)
{
lean_object* v_pre_3475_; 
v_pre_3475_ = lean_ctor_get(v_pre_3474_, 0);
if (lean_obj_tag(v_pre_3475_) == 0)
{
lean_object* v_type_3476_; lean_object* v_args_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3547_; 
v_type_3476_ = lean_ctor_get(v_decl_3415_, 2);
v_args_3477_ = lean_ctor_get(v_value_3472_, 2);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_value_3472_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; lean_object* v_unused_3549_; 
v_unused_3548_ = lean_ctor_get(v_value_3472_, 1);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_value_3472_, 0);
lean_dec(v_unused_3549_);
v___x_3479_ = v_value_3472_;
v_isShared_3480_ = v_isSharedCheck_3547_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_args_3477_);
lean_dec(v_value_3472_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3547_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v_str_3481_; lean_object* v_str_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v_str_3481_ = lean_ctor_get(v_declName_3473_, 1);
lean_inc_ref(v_str_3481_);
lean_dec_ref_known(v_declName_3473_, 2);
v_str_3482_ = lean_ctor_get(v_pre_3474_, 1);
lean_inc_ref(v_str_3482_);
lean_dec_ref_known(v_pre_3474_, 2);
v___x_3483_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__5));
v___x_3484_ = lean_string_dec_eq(v_str_3482_, v___x_3483_);
lean_dec_ref(v_str_3482_);
if (v___x_3484_ == 0)
{
lean_dec_ref(v_str_3481_);
lean_del_object(v___x_3479_);
lean_dec_ref(v_args_3477_);
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
goto v___jp_3417_;
}
else
{
lean_object* v___x_3485_; uint8_t v___x_3486_; 
v___x_3485_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_3486_ = lean_string_dec_eq(v_str_3481_, v___x_3485_);
lean_dec_ref(v_str_3481_);
if (v___x_3486_ == 0)
{
lean_del_object(v___x_3479_);
lean_dec_ref(v_args_3477_);
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
goto v___jp_3417_;
}
else
{
lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3544_; 
lean_inc_ref(v_type_3476_);
lean_inc_ref(v_k_3416_);
lean_inc_ref(v_decl_3415_);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3544_ == 0)
{
lean_object* v_unused_3545_; lean_object* v_unused_3546_; 
v_unused_3545_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3545_);
v_unused_3546_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3546_);
v___x_3488_ = v_code_3291_;
v_isShared_3489_ = v_isSharedCheck_3544_;
goto v_resetjp_3487_;
}
else
{
lean_dec(v_code_3291_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3544_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = lean_array_get_size(v_args_3477_);
v___x_3491_ = lean_unsigned_to_nat(1u);
v___x_3492_ = lean_nat_dec_eq(v___x_3490_, v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec_ref(v_args_3477_);
lean_dec_ref(v_type_3476_);
lean_dec_ref(v_k_3416_);
lean_dec_ref(v_decl_3415_);
v___x_3493_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3494_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3493_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3494_;
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = lean_array_fget(v_args_3477_, v___x_3495_);
lean_dec_ref(v_args_3477_);
v___x_3497_ = 0;
v___x_3498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3499_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_3500_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3497_, v___x_3498_, v___x_3499_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v_fvarId_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v_fvarId_3502_ = lean_ctor_get(v_a_3501_, 0);
v___x_3503_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3504_ = lean_box(0);
lean_inc(v_fvarId_3502_);
v___x_3505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_fvarId_3502_);
v___x_3506_ = lean_unsigned_to_nat(2u);
v___x_3507_ = lean_mk_empty_array_with_capacity(v___x_3506_);
v___x_3508_ = lean_array_push(v___x_3507_, v___x_3496_);
v___x_3509_ = lean_array_push(v___x_3508_, v___x_3505_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 2, v___x_3509_);
lean_ctor_set(v___x_3479_, 1, v___x_3504_);
lean_ctor_set(v___x_3479_, 0, v___x_3503_);
v___x_3511_ = v___x_3479_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3503_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v___x_3504_);
lean_ctor_set(v_reuseFailAlloc_3535_, 2, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3512_; 
v___x_3512_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3497_, v_decl_3415_, v_type_3476_, v___x_3511_, v_a_3294_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3514_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___x_3514_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3416_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3526_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3517_ = v___x_3514_;
v_isShared_3518_ = v_isSharedCheck_3526_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3514_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3526_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 1, v_a_3515_);
lean_ctor_set(v___x_3488_, 0, v_a_3513_);
v___x_3520_ = v___x_3488_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3513_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_a_3501_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 0, v___x_3521_);
v___x_3523_ = v___x_3517_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_dec(v_a_3513_);
lean_dec(v_a_3501_);
lean_del_object(v___x_3488_);
return v___x_3514_;
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3501_);
lean_del_object(v___x_3488_);
lean_dec_ref(v_k_3416_);
v_a_3527_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3512_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3512_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v___x_3496_);
lean_del_object(v___x_3488_);
lean_del_object(v___x_3479_);
lean_dec_ref(v_type_3476_);
lean_dec_ref(v_k_3416_);
lean_dec_ref(v_decl_3415_);
v_a_3536_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3500_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3500_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
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
lean_dec_ref_known(v_pre_3474_, 2);
lean_dec_ref_known(v_declName_3473_, 2);
lean_dec_ref_known(v_value_3472_, 3);
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
goto v___jp_3417_;
}
}
else
{
lean_dec(v_pre_3474_);
lean_dec_ref_known(v_declName_3473_, 2);
lean_dec_ref_known(v_value_3472_, 3);
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
goto v___jp_3417_;
}
}
else
{
lean_dec(v_declName_3473_);
lean_dec_ref_known(v_value_3472_, 3);
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
goto v___jp_3417_;
}
}
else
{
lean_dec(v_value_3472_);
v___y_3418_ = v_a_3292_;
v___y_3419_ = v_a_3293_;
v___y_3420_ = v_a_3294_;
v___y_3421_ = v_a_3295_;
v___y_3422_ = v_a_3296_;
goto v___jp_3417_;
}
v___jp_3417_:
{
lean_object* v___x_3423_; 
lean_inc_ref(v_decl_3415_);
v___x_3423_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3415_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
lean_inc_ref(v_k_3416_);
v___x_3425_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3416_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3463_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3463_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3463_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
size_t v___x_3430_; size_t v___x_3431_; uint8_t v___x_3432_; 
v___x_3430_ = lean_ptr_addr(v_k_3416_);
v___x_3431_ = lean_ptr_addr(v_a_3426_);
v___x_3432_ = lean_usize_dec_eq(v___x_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3442_; 
v_isSharedCheck_3442_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; lean_object* v_unused_3444_; 
v_unused_3443_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3443_);
v_unused_3444_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3444_);
v___x_3434_ = v_code_3291_;
v_isShared_3435_ = v_isSharedCheck_3442_;
goto v_resetjp_3433_;
}
else
{
lean_dec(v_code_3291_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3442_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 1, v_a_3426_);
lean_ctor_set(v___x_3434_, 0, v_a_3424_);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3424_);
lean_ctor_set(v_reuseFailAlloc_3441_, 1, v_a_3426_);
v___x_3437_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
lean_object* v___x_3439_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3437_);
v___x_3439_ = v___x_3428_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
else
{
size_t v___x_3445_; size_t v___x_3446_; uint8_t v___x_3447_; 
v___x_3445_ = lean_ptr_addr(v_decl_3415_);
v___x_3446_ = lean_ptr_addr(v_a_3424_);
v___x_3447_ = lean_usize_dec_eq(v___x_3445_, v___x_3446_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3457_; 
v_isSharedCheck_3457_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3457_ == 0)
{
lean_object* v_unused_3458_; lean_object* v_unused_3459_; 
v_unused_3458_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3458_);
v_unused_3459_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3459_);
v___x_3449_ = v_code_3291_;
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v_code_3291_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 1, v_a_3426_);
lean_ctor_set(v___x_3449_, 0, v_a_3424_);
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3424_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_a_3426_);
v___x_3452_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v___x_3452_);
v___x_3454_ = v___x_3428_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v___x_3461_; 
lean_dec(v_a_3426_);
lean_dec(v_a_3424_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 0, v_code_3291_);
v___x_3461_ = v___x_3428_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_code_3291_);
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
lean_dec(v_a_3424_);
lean_dec_ref_known(v_code_3291_, 2);
return v___x_3425_;
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref_known(v_code_3291_, 2);
v_a_3464_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3423_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3423_);
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
case 3:
{
lean_object* v_fvarId_3550_; lean_object* v_args_3551_; size_t v_sz_3552_; size_t v___x_3553_; lean_object* v___x_3554_; 
v_fvarId_3550_ = lean_ctor_get(v_code_3291_, 0);
v_args_3551_ = lean_ctor_get(v_code_3291_, 1);
v_sz_3552_ = lean_array_size(v_args_3551_);
v___x_3553_ = ((size_t)0ULL);
lean_inc_ref(v_args_3551_);
v___x_3554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3552_, v___x_3553_, v_args_3551_, v_a_3292_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3590_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3590_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3590_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
uint8_t v___x_3559_; 
v___x_3559_ = l_Lean_instBEqFVarId_beq(v_fvarId_3550_, v_fvarId_3550_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3569_; 
lean_inc(v_fvarId_3550_);
v_isSharedCheck_3569_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; lean_object* v_unused_3571_; 
v_unused_3570_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3571_);
v___x_3561_ = v_code_3291_;
v_isShared_3562_ = v_isSharedCheck_3569_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v_code_3291_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3569_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 1, v_a_3555_);
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_fvarId_3550_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_a_3555_);
v___x_3564_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3566_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3564_);
v___x_3566_ = v___x_3557_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
size_t v___x_3572_; size_t v___x_3573_; uint8_t v___x_3574_; 
v___x_3572_ = lean_ptr_addr(v_args_3551_);
v___x_3573_ = lean_ptr_addr(v_a_3555_);
v___x_3574_ = lean_usize_dec_eq(v___x_3572_, v___x_3573_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3584_; 
lean_inc(v_fvarId_3550_);
v_isSharedCheck_3584_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; lean_object* v_unused_3586_; 
v_unused_3585_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3585_);
v_unused_3586_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3586_);
v___x_3576_ = v_code_3291_;
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
else
{
lean_dec(v_code_3291_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v_a_3555_);
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_fvarId_3550_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_a_3555_);
v___x_3579_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; 
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v___x_3579_);
v___x_3581_ = v___x_3557_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_object* v___x_3588_; 
lean_dec(v_a_3555_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 0, v_code_3291_);
v___x_3588_ = v___x_3557_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_code_3291_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref_known(v_code_3291_, 2);
v_a_3591_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3554_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3554_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
case 4:
{
lean_object* v_cases_3599_; lean_object* v_typeName_3600_; lean_object* v_resultType_3601_; lean_object* v_discr_3602_; lean_object* v_alts_3603_; lean_object* v___x_3604_; uint8_t v___x_3605_; 
v_cases_3599_ = lean_ctor_get(v_code_3291_, 0);
lean_inc_ref(v_cases_3599_);
v_typeName_3600_ = lean_ctor_get(v_cases_3599_, 0);
v_resultType_3601_ = lean_ctor_get(v_cases_3599_, 1);
v_discr_3602_ = lean_ctor_get(v_cases_3599_, 2);
v_alts_3603_ = lean_ctor_get(v_cases_3599_, 3);
v___x_3604_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3605_ = lean_name_eq(v_typeName_3600_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3607_ = lean_name_eq(v_typeName_3600_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; uint8_t v___x_3609_; 
v___x_3608_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__9));
v___x_3609_ = lean_name_eq(v_typeName_3600_, v___x_3608_);
if (v___x_3609_ == 0)
{
lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3610_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__11));
v___x_3611_ = lean_name_eq(v_typeName_3600_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3612_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__13));
v___x_3613_ = lean_name_eq(v_typeName_3600_, v___x_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; uint8_t v___x_3615_; 
v___x_3614_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__15));
v___x_3615_ = lean_name_eq(v_typeName_3600_, v___x_3614_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; uint8_t v___x_3617_; 
v___x_3616_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3617_ = lean_name_eq(v_typeName_3600_, v___x_3616_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; uint8_t v___x_3619_; 
v___x_3618_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3619_ = lean_name_eq(v_typeName_3600_, v___x_3618_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; uint8_t v___x_3621_; 
v___x_3620_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3621_ = lean_name_eq(v_typeName_3600_, v___x_3620_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3623_ = lean_name_eq(v_typeName_3600_, v___x_3622_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; uint8_t v___x_3625_; 
v___x_3624_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3625_ = lean_name_eq(v_typeName_3600_, v___x_3624_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; uint8_t v___x_3627_; 
v___x_3626_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3627_ = lean_name_eq(v_typeName_3600_, v___x_3626_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; uint8_t v___x_3629_; 
v___x_3628_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3629_ = lean_name_eq(v_typeName_3600_, v___x_3628_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; uint8_t v___x_3631_; 
v___x_3630_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__24));
v___x_3631_ = lean_name_eq(v_typeName_3600_, v___x_3630_);
if (v___x_3631_ == 0)
{
lean_object* v___x_3632_; uint8_t v___x_3633_; 
v___x_3632_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__25));
v___x_3633_ = lean_name_eq(v_typeName_3600_, v___x_3632_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; 
lean_inc(v_typeName_3600_);
v___x_3634_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3600_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
lean_inc(v_a_3635_);
lean_dec_ref_known(v___x_3634_, 1);
if (lean_obj_tag(v_a_3635_) == 1)
{
lean_object* v_val_3636_; lean_object* v___x_3637_; 
lean_dec_ref_known(v_code_3291_, 1);
v_val_3636_ = lean_ctor_get(v_a_3635_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_a_3635_, 1);
v___x_3637_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3636_, v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec(v_val_3636_);
return v___x_3637_;
}
else
{
lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3736_; 
lean_inc_ref(v_alts_3603_);
lean_inc(v_discr_3602_);
lean_inc_ref(v_resultType_3601_);
lean_inc(v_typeName_3600_);
lean_dec(v_a_3635_);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_cases_3599_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; 
v_unused_3737_ = lean_ctor_get(v_cases_3599_, 3);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_cases_3599_, 2);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_cases_3599_, 1);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_cases_3599_, 0);
lean_dec(v_unused_3740_);
v___x_3639_ = v_cases_3599_;
v_isShared_3640_ = v_isSharedCheck_3736_;
goto v_resetjp_3638_;
}
else
{
lean_dec(v_cases_3599_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3736_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; 
lean_inc_ref(v_resultType_3601_);
v___x_3641_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3601_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3727_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3727_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3727_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v_env_3647_; lean_object* v___x_3648_; 
v___x_3646_ = lean_st_ref_get(v_a_3296_);
v_env_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc_ref_n(v_env_3647_, 2);
lean_dec(v___x_3646_);
lean_inc(v_typeName_3600_);
v___x_3648_ = l_Lean_Environment_find_x3f(v_env_3647_, v_typeName_3600_, v___x_3633_);
if (lean_obj_tag(v___x_3648_) == 1)
{
lean_object* v_val_3649_; 
v_val_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_val_3649_);
lean_dec_ref_known(v___x_3648_, 1);
if (lean_obj_tag(v_val_3649_) == 5)
{
lean_object* v_val_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3726_; 
v_val_3650_ = lean_ctor_get(v_val_3649_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_val_3649_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3652_ = v_val_3649_;
v_isShared_3653_ = v_isSharedCheck_3726_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_val_3650_);
lean_dec(v_val_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3726_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_toConstantVal_3654_; lean_object* v_name_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_toConstantVal_3654_ = lean_ctor_get(v_val_3650_, 0);
lean_inc_ref(v_toConstantVal_3654_);
lean_dec_ref(v_val_3650_);
v_name_3655_ = lean_ctor_get(v_toConstantVal_3654_, 0);
lean_inc(v_name_3655_);
lean_dec_ref(v_toConstantVal_3654_);
v___x_3656_ = l_Lean_mkCasesOnName(v_name_3655_);
lean_inc_ref(v_env_3647_);
v___x_3657_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3647_, v___x_3656_);
if (lean_obj_tag(v___x_3657_) == 0)
{
size_t v_sz_3658_; size_t v___x_3659_; lean_object* v___x_3660_; 
lean_dec_ref(v_env_3647_);
v_sz_3658_ = lean_array_size(v_alts_3603_);
v___x_3659_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3603_);
v___x_3660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_sz_3658_, v___x_3659_, v_alts_3603_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3685_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3685_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3685_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
size_t v___x_3675_; size_t v___x_3676_; uint8_t v___x_3677_; 
v___x_3675_ = lean_ptr_addr(v_alts_3603_);
lean_dec_ref(v_alts_3603_);
v___x_3676_ = lean_ptr_addr(v_a_3661_);
v___x_3677_ = lean_usize_dec_eq(v___x_3675_, v___x_3676_);
if (v___x_3677_ == 0)
{
lean_del_object(v___x_3644_);
lean_dec_ref(v_resultType_3601_);
lean_dec_ref_known(v_code_3291_, 1);
goto v___jp_3665_;
}
else
{
size_t v___x_3678_; size_t v___x_3679_; uint8_t v___x_3680_; 
v___x_3678_ = lean_ptr_addr(v_resultType_3601_);
lean_dec_ref(v_resultType_3601_);
v___x_3679_ = lean_ptr_addr(v_a_3642_);
v___x_3680_ = lean_usize_dec_eq(v___x_3678_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_del_object(v___x_3644_);
lean_dec_ref_known(v_code_3291_, 1);
goto v___jp_3665_;
}
else
{
uint8_t v___x_3681_; 
v___x_3681_ = l_Lean_instBEqFVarId_beq(v_discr_3602_, v_discr_3602_);
if (v___x_3681_ == 0)
{
lean_del_object(v___x_3644_);
lean_dec_ref_known(v_code_3291_, 1);
goto v___jp_3665_;
}
else
{
lean_object* v___x_3683_; 
lean_del_object(v___x_3663_);
lean_dec(v_a_3661_);
lean_del_object(v___x_3652_);
lean_dec(v_a_3642_);
lean_del_object(v___x_3639_);
lean_dec(v_discr_3602_);
lean_dec(v_typeName_3600_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_code_3291_);
v___x_3683_ = v___x_3644_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_code_3291_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
v___jp_3665_:
{
lean_object* v___x_3667_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 3, v_a_3661_);
lean_ctor_set(v___x_3639_, 1, v_a_3642_);
v___x_3667_ = v___x_3639_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_typeName_3600_);
lean_ctor_set(v_reuseFailAlloc_3674_, 1, v_a_3642_);
lean_ctor_set(v_reuseFailAlloc_3674_, 2, v_discr_3602_);
lean_ctor_set(v_reuseFailAlloc_3674_, 3, v_a_3661_);
v___x_3667_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3669_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set_tag(v___x_3652_, 4);
lean_ctor_set(v___x_3652_, 0, v___x_3667_);
v___x_3669_ = v___x_3652_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3667_);
v___x_3669_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3671_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3669_);
v___x_3671_ = v___x_3663_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_del_object(v___x_3652_);
lean_del_object(v___x_3644_);
lean_dec(v_a_3642_);
lean_del_object(v___x_3639_);
lean_dec_ref(v_alts_3603_);
lean_dec(v_discr_3602_);
lean_dec_ref(v_resultType_3601_);
lean_dec(v_typeName_3600_);
lean_dec_ref_known(v_code_3291_, 1);
v_a_3686_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3660_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3660_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref_known(v___x_3657_, 1);
lean_del_object(v___x_3652_);
lean_del_object(v___x_3644_);
lean_dec_ref(v_resultType_3601_);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3725_);
v___x_3695_ = v_code_3291_;
v_isShared_3696_ = v_isSharedCheck_3724_;
goto v_resetjp_3694_;
}
else
{
lean_dec(v_code_3291_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3724_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; size_t v_sz_3699_; size_t v___x_3700_; lean_object* v___x_3701_; 
v___x_3697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___closed__4));
v___x_3698_ = l_Lean_Name_append(v_typeName_3600_, v___x_3697_);
v_sz_3699_ = lean_array_size(v_alts_3603_);
v___x_3700_ = ((size_t)0ULL);
v___x_3701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_env_3647_, v___x_3633_, v_sz_3699_, v___x_3700_, v_alts_3603_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3715_; 
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3715_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3715_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3640_ == 0)
{
lean_ctor_set(v___x_3639_, 3, v_a_3702_);
lean_ctor_set(v___x_3639_, 1, v_a_3642_);
lean_ctor_set(v___x_3639_, 0, v___x_3698_);
v___x_3707_ = v___x_3639_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_a_3642_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_discr_3602_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3709_; 
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3707_);
v___x_3709_ = v___x_3695_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3707_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3711_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3709_);
v___x_3711_ = v___x_3704_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v___x_3698_);
lean_del_object(v___x_3695_);
lean_dec(v_a_3642_);
lean_del_object(v___x_3639_);
lean_dec(v_discr_3602_);
v_a_3716_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3701_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3701_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
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
}
}
}
else
{
lean_dec(v_val_3649_);
lean_dec_ref(v_env_3647_);
lean_del_object(v___x_3644_);
lean_dec(v_a_3642_);
lean_del_object(v___x_3639_);
lean_dec_ref(v_alts_3603_);
lean_dec(v_discr_3602_);
lean_dec_ref(v_resultType_3601_);
lean_dec(v_typeName_3600_);
lean_dec_ref_known(v_code_3291_, 1);
v___y_3299_ = v_a_3292_;
v___y_3300_ = v_a_3293_;
v___y_3301_ = v_a_3294_;
v___y_3302_ = v_a_3295_;
v___y_3303_ = v_a_3296_;
goto v___jp_3298_;
}
}
else
{
lean_dec(v___x_3648_);
lean_dec_ref(v_env_3647_);
lean_del_object(v___x_3644_);
lean_dec(v_a_3642_);
lean_del_object(v___x_3639_);
lean_dec_ref(v_alts_3603_);
lean_dec(v_discr_3602_);
lean_dec_ref(v_resultType_3601_);
lean_dec(v_typeName_3600_);
lean_dec_ref_known(v_code_3291_, 1);
v___y_3299_ = v_a_3292_;
v___y_3300_ = v_a_3293_;
v___y_3301_ = v_a_3294_;
v___y_3302_ = v_a_3295_;
v___y_3303_ = v_a_3296_;
goto v___jp_3298_;
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_del_object(v___x_3639_);
lean_dec_ref(v_alts_3603_);
lean_dec(v_discr_3602_);
lean_dec_ref(v_resultType_3601_);
lean_dec(v_typeName_3600_);
lean_dec_ref_known(v_code_3291_, 1);
v_a_3728_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3641_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3641_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref_known(v_code_3291_, 1);
lean_dec_ref(v_cases_3599_);
v_a_3741_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3634_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3634_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v___x_3749_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3749_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3749_;
}
}
else
{
lean_object* v___x_3750_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3750_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec_ref(v_cases_3599_);
return v___x_3750_;
}
}
else
{
lean_object* v___x_3751_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3751_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3751_;
}
}
else
{
lean_object* v___x_3752_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3752_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3752_;
}
}
else
{
lean_object* v___x_3753_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3753_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3753_;
}
}
else
{
lean_object* v___x_3754_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3754_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3754_;
}
}
else
{
lean_object* v___x_3755_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3755_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3755_;
}
}
else
{
lean_object* v___x_3756_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3756_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3756_;
}
}
else
{
lean_object* v___x_3757_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3757_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3599_, v___x_3616_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3757_;
}
}
else
{
lean_object* v___x_3758_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3758_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3599_, v___x_3614_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3758_;
}
}
else
{
lean_object* v___x_3759_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3759_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3599_, v___x_3612_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3759_;
}
}
else
{
lean_object* v___x_3760_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3760_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3599_, v___x_3610_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3760_;
}
}
else
{
lean_object* v___x_3761_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3761_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3599_, v___x_3608_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3761_;
}
}
else
{
lean_object* v___x_3762_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3762_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3762_;
}
}
else
{
lean_object* v___x_3763_; 
lean_dec_ref_known(v_code_3291_, 1);
v___x_3763_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3599_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
return v___x_3763_;
}
}
case 5:
{
lean_object* v___x_3764_; 
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_code_3291_);
return v___x_3764_;
}
case 6:
{
lean_object* v_type_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3789_; 
v_type_3765_ = lean_ctor_get(v_code_3291_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3767_ = v_code_3291_;
v_isShared_3768_ = v_isSharedCheck_3789_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_type_3765_);
lean_dec(v_code_3291_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3789_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3765_, v_a_3295_, v_a_3296_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3780_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3780_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3780_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v_a_3770_);
v___x_3775_ = v___x_3767_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
lean_object* v___x_3777_; 
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3775_);
v___x_3777_ = v___x_3772_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_del_object(v___x_3767_);
v_a_3781_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3769_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3769_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
default: 
{
lean_object* v_decl_3790_; lean_object* v_k_3791_; 
v_decl_3790_ = lean_ctor_get(v_code_3291_, 0);
v_k_3791_ = lean_ctor_get(v_code_3291_, 1);
lean_inc_ref(v_k_3791_);
lean_inc_ref(v_decl_3790_);
v_decl_3307_ = v_decl_3790_;
v_k_3308_ = v_k_3791_;
v___y_3309_ = v_a_3292_;
v___y_3310_ = v_a_3293_;
v___y_3311_ = v_a_3294_;
v___y_3312_ = v_a_3295_;
v___y_3313_ = v_a_3296_;
goto v___jp_3306_;
}
}
v___jp_3298_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__1, &l_Lean_Compiler_LCNF_Code_toMono___closed__1_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__1);
v___x_3305_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3304_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
return v___x_3305_;
}
v___jp_3306_:
{
lean_object* v___x_3314_; 
v___x_3314_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3307_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref_known(v___x_3314_, 1);
v___x_3316_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
if (lean_obj_tag(v___x_3316_) == 0)
{
switch(lean_obj_tag(v_code_3291_))
{
case 1:
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3356_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3356_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3356_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_decl_3321_; lean_object* v_k_3322_; size_t v___x_3323_; size_t v___x_3324_; uint8_t v___x_3325_; 
v_decl_3321_ = lean_ctor_get(v_code_3291_, 0);
v_k_3322_ = lean_ctor_get(v_code_3291_, 1);
v___x_3323_ = lean_ptr_addr(v_k_3322_);
v___x_3324_ = lean_ptr_addr(v_a_3317_);
v___x_3325_ = lean_usize_dec_eq(v___x_3323_, v___x_3324_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3335_; 
v_isSharedCheck_3335_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; lean_object* v_unused_3337_; 
v_unused_3336_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3336_);
v_unused_3337_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3337_);
v___x_3327_ = v_code_3291_;
v_isShared_3328_ = v_isSharedCheck_3335_;
goto v_resetjp_3326_;
}
else
{
lean_dec(v_code_3291_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3335_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v_a_3317_);
lean_ctor_set(v___x_3327_, 0, v_a_3315_);
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3315_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_a_3317_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3330_);
v___x_3332_ = v___x_3319_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
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
size_t v___x_3338_; size_t v___x_3339_; uint8_t v___x_3340_; 
v___x_3338_ = lean_ptr_addr(v_decl_3321_);
v___x_3339_ = lean_ptr_addr(v_a_3315_);
v___x_3340_ = lean_usize_dec_eq(v___x_3338_, v___x_3339_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3350_; 
v_isSharedCheck_3350_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; lean_object* v_unused_3352_; 
v_unused_3351_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3352_);
v___x_3342_ = v_code_3291_;
v_isShared_3343_ = v_isSharedCheck_3350_;
goto v_resetjp_3341_;
}
else
{
lean_dec(v_code_3291_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3350_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 1, v_a_3317_);
lean_ctor_set(v___x_3342_, 0, v_a_3315_);
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3315_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3317_);
v___x_3345_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3347_; 
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v___x_3345_);
v___x_3347_ = v___x_3319_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
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
else
{
lean_object* v___x_3354_; 
lean_dec(v_a_3317_);
lean_dec(v_a_3315_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 0, v_code_3291_);
v___x_3354_ = v___x_3319_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_code_3291_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
case 2:
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3396_; 
v_a_3357_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3359_ = v___x_3316_;
v_isShared_3360_ = v_isSharedCheck_3396_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3316_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3396_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v_decl_3361_; lean_object* v_k_3362_; size_t v___x_3363_; size_t v___x_3364_; uint8_t v___x_3365_; 
v_decl_3361_ = lean_ctor_get(v_code_3291_, 0);
v_k_3362_ = lean_ctor_get(v_code_3291_, 1);
v___x_3363_ = lean_ptr_addr(v_k_3362_);
v___x_3364_ = lean_ptr_addr(v_a_3357_);
v___x_3365_ = lean_usize_dec_eq(v___x_3363_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3375_; 
v_isSharedCheck_3375_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; lean_object* v_unused_3377_; 
v_unused_3376_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3376_);
v_unused_3377_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3377_);
v___x_3367_ = v_code_3291_;
v_isShared_3368_ = v_isSharedCheck_3375_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v_code_3291_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3375_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 1, v_a_3357_);
lean_ctor_set(v___x_3367_, 0, v_a_3315_);
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3315_);
lean_ctor_set(v_reuseFailAlloc_3374_, 1, v_a_3357_);
v___x_3370_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
lean_object* v___x_3372_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3370_);
v___x_3372_ = v___x_3359_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
size_t v___x_3378_; size_t v___x_3379_; uint8_t v___x_3380_; 
v___x_3378_ = lean_ptr_addr(v_decl_3361_);
v___x_3379_ = lean_ptr_addr(v_a_3315_);
v___x_3380_ = lean_usize_dec_eq(v___x_3378_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3390_; 
v_isSharedCheck_3390_ = !lean_is_exclusive(v_code_3291_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; lean_object* v_unused_3392_; 
v_unused_3391_ = lean_ctor_get(v_code_3291_, 1);
lean_dec(v_unused_3391_);
v_unused_3392_ = lean_ctor_get(v_code_3291_, 0);
lean_dec(v_unused_3392_);
v___x_3382_ = v_code_3291_;
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
else
{
lean_dec(v_code_3291_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 1, v_a_3357_);
lean_ctor_set(v___x_3382_, 0, v_a_3315_);
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3315_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3357_);
v___x_3385_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3385_);
v___x_3387_ = v___x_3359_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
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
else
{
lean_object* v___x_3394_; 
lean_dec(v_a_3357_);
lean_dec(v_a_3315_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v_code_3291_);
v___x_3394_ = v___x_3359_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_code_3291_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
default: 
{
lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_a_3315_);
lean_dec_ref(v_code_3291_);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3405_ == 0)
{
lean_object* v_unused_3406_; 
v_unused_3406_ = lean_ctor_get(v___x_3316_, 0);
lean_dec(v_unused_3406_);
v___x_3398_ = v___x_3316_;
v_isShared_3399_ = v_isSharedCheck_3405_;
goto v_resetjp_3397_;
}
else
{
lean_dec(v___x_3316_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3405_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v___x_3400_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3401_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3400_);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3401_);
v___x_3403_ = v___x_3398_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
else
{
lean_dec(v_a_3315_);
lean_dec_ref(v_code_3291_);
return v___x_3316_;
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v_k_3308_);
lean_dec_ref(v_code_3291_);
v_a_3407_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3314_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3314_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_){
_start:
{
lean_object* v_params_3799_; lean_object* v_type_3800_; lean_object* v_value_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; 
v_params_3799_ = lean_ctor_get(v_decl_3792_, 2);
v_type_3800_ = lean_ctor_get(v_decl_3792_, 3);
v_value_3801_ = lean_ctor_get(v_decl_3792_, 4);
v___x_3802_ = 0;
lean_inc_ref(v_type_3800_);
v___x_3803_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3800_, v_a_3796_, v_a_3797_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; size_t v_sz_3805_; size_t v___x_3806_; lean_object* v___x_3807_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v_sz_3805_ = lean_array_size(v_params_3799_);
v___x_3806_ = ((size_t)0ULL);
lean_inc_ref(v_params_3799_);
v___x_3807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_3805_, v___x_3806_, v_params_3799_, v_a_3793_, v_a_3795_, v_a_3796_, v_a_3797_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3809_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
lean_inc_ref(v_value_3801_);
v___x_3809_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_3801_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3802_, v_decl_3792_, v_a_3804_, v_a_3808_, v_a_3810_, v_a_3795_);
return v___x_3811_;
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec(v_a_3808_);
lean_dec(v_a_3804_);
lean_dec_ref(v_decl_3792_);
v_a_3812_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3809_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3809_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_a_3804_);
lean_dec_ref(v_decl_3792_);
v_a_3820_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3807_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3807_);
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
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v_decl_3792_);
v_a_3828_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3803_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3803_);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_sz_3844_, lean_object* v_i_3845_, lean_object* v_bs_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
size_t v_sz_boxed_3853_; size_t v_i_boxed_3854_; lean_object* v_res_3855_; 
v_sz_boxed_3853_ = lean_unbox_usize(v_sz_3844_);
lean_dec(v_sz_3844_);
v_i_boxed_3854_ = lean_unbox_usize(v_i_3845_);
lean_dec(v_i_3845_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_sz_boxed_3853_, v_i_boxed_3854_, v_bs_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_3864_, lean_object* v_uintName_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_3864_, v_uintName_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
lean_dec(v_a_3876_);
lean_dec_ref(v_a_3875_);
lean_dec(v_a_3874_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v_res_3912_; 
v_res_3912_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v___x_3913_, lean_object* v___x_3914_, lean_object* v_sz_3915_, lean_object* v_i_3916_, lean_object* v_bs_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
uint8_t v___x_33864__boxed_3924_; size_t v_sz_boxed_3925_; size_t v_i_boxed_3926_; lean_object* v_res_3927_; 
v___x_33864__boxed_3924_ = lean_unbox(v___x_3914_);
v_sz_boxed_3925_ = lean_unbox_usize(v_sz_3915_);
lean_dec(v_sz_3915_);
v_i_boxed_3926_ = lean_unbox_usize(v_i_3916_);
lean_dec(v_i_3916_);
v_res_3927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v___x_3913_, v___x_33864__boxed_3924_, v_sz_boxed_3925_, v_i_boxed_3926_, v_bs_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_){
_start:
{
lean_object* v_res_3935_; 
v_res_3935_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
return v_res_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
lean_dec(v_a_3949_);
lean_dec_ref(v_a_3948_);
lean_dec(v_a_3947_);
lean_dec_ref(v_a_3946_);
lean_dec(v_a_3945_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_3952_, lean_object* v_c_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_3952_, v_c_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
lean_dec(v_a_3954_);
lean_dec_ref(v_info_3952_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_3961_, lean_object* v_sz_3962_, lean_object* v_i_3963_, lean_object* v_bs_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
size_t v_sz_boxed_3971_; size_t v_i_boxed_3972_; lean_object* v_res_3973_; 
v_sz_boxed_3971_ = lean_unbox_usize(v_sz_3962_);
lean_dec(v_sz_3962_);
v_i_boxed_3972_ = lean_unbox_usize(v_i_3963_);
lean_dec(v_i_3963_);
v_res_3973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3961_, v_sz_boxed_3971_, v_i_boxed_3972_, v_bs_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_c_3974_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_3982_, lean_object* v_sz_3983_, lean_object* v_i_3984_, lean_object* v_bs_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
size_t v_sz_boxed_3992_; size_t v_i_boxed_3993_; lean_object* v_res_3994_; 
v_sz_boxed_3992_ = lean_unbox_usize(v_sz_3983_);
lean_dec(v_sz_3983_);
v_i_boxed_3993_ = lean_unbox_usize(v_i_3984_);
lean_dec(v_i_3984_);
v_res_3994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3982_, v_sz_boxed_3992_, v_i_boxed_3993_, v_bs_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4003_, lean_object* v_x_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4003_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4012_, lean_object* v_x_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4012_, v_x_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4021_, lean_object* v_x_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4021_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4030_, lean_object* v_x_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4030_, v_x_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_c_4030_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4039_, lean_object* v_x_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4039_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4048_, lean_object* v_x_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4048_, v_x_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec(v_a_4054_);
lean_dec_ref(v_a_4053_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
lean_dec(v_a_4050_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4057_, lean_object* v_x_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4057_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4066_, lean_object* v_x_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4066_, v_x_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec(v_a_4072_);
lean_dec_ref(v_a_4071_);
lean_dec(v_a_4070_);
lean_dec_ref(v_a_4069_);
lean_dec(v_a_4068_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4075_, lean_object* v_x_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4075_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4084_, lean_object* v_x_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4084_, v_x_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_);
lean_dec(v_a_4090_);
lean_dec_ref(v_a_4089_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
lean_dec(v_a_4086_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4093_, lean_object* v_x_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4093_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4102_, lean_object* v_x_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4102_, v_x_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_);
lean_dec(v_a_4108_);
lean_dec_ref(v_a_4107_);
lean_dec(v_a_4106_);
lean_dec_ref(v_a_4105_);
lean_dec(v_a_4104_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4111_, lean_object* v_x_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4111_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4120_, lean_object* v_x_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4120_, v_x_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4129_, lean_object* v_x_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4129_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4138_, lean_object* v_x_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4138_, v_x_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4147_, lean_object* v_uintName_4148_, lean_object* v_x_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v___x_4156_; 
v___x_4156_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4147_, v_uintName_4148_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4157_, lean_object* v_uintName_4158_, lean_object* v_x_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4157_, v_uintName_4158_, v_x_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
lean_dec(v_a_4160_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4167_, lean_object* v_x_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4167_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4176_, lean_object* v_x_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4176_, v_x_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_);
lean_dec(v_a_4182_);
lean_dec_ref(v_a_4181_);
lean_dec(v_a_4180_);
lean_dec_ref(v_a_4179_);
lean_dec(v_a_4178_);
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4185_, lean_object* v_x_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4185_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4194_, lean_object* v_x_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4194_, v_x_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_);
lean_dec(v_a_4200_);
lean_dec_ref(v_a_4199_);
lean_dec(v_a_4198_);
lean_dec_ref(v_a_4197_);
lean_dec(v_a_4196_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4203_, size_t v_i_4204_, lean_object* v_bs_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4203_, v_i_4204_, v_bs_4205_, v___y_4206_, v___y_4208_, v___y_4209_, v___y_4210_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4213_, lean_object* v_i_4214_, lean_object* v_bs_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
size_t v_sz_boxed_4222_; size_t v_i_boxed_4223_; lean_object* v_res_4224_; 
v_sz_boxed_4222_ = lean_unbox_usize(v_sz_4213_);
lean_dec(v_sz_4213_);
v_i_boxed_4223_ = lean_unbox_usize(v_i_4214_);
lean_dec(v_i_4214_);
v_res_4224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4222_, v_i_boxed_4223_, v_bs_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4225_, lean_object* v_v_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
if (lean_obj_tag(v_v_4226_) == 0)
{
lean_object* v_code_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4257_; 
v_code_4233_ = lean_ctor_get(v_v_4226_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v_v_4226_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4235_ = v_v_4226_;
v_isShared_4236_ = v_isSharedCheck_4257_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_code_4233_);
lean_dec(v_v_4226_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4257_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; 
lean_inc(v___y_4231_);
lean_inc_ref(v___y_4230_);
lean_inc(v___y_4229_);
lean_inc_ref(v___y_4228_);
lean_inc(v___y_4227_);
v___x_4237_ = lean_apply_7(v_f_4225_, v_code_4233_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, lean_box(0));
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4248_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4248_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4248_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v_a_4238_);
v___x_4243_ = v___x_4235_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
lean_object* v___x_4245_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set(v___x_4240_, 0, v___x_4243_);
v___x_4245_ = v___x_4240_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4243_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_del_object(v___x_4235_);
v_a_4249_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4237_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4237_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
}
else
{
lean_object* v___x_4258_; 
lean_dec_ref(v_f_4225_);
v___x_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4258_, 0, v_v_4226_);
return v___x_4258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4259_, lean_object* v_v_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4259_, v_v_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4268_, lean_object* v_f_4269_, lean_object* v_v_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4269_, v_v_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4278_, lean_object* v_f_4279_, lean_object* v_v_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_){
_start:
{
uint8_t v_pu_boxed_4287_; lean_object* v_res_4288_; 
v_pu_boxed_4287_ = lean_unbox(v_pu_4278_);
v_res_4288_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4287_, v_f_4279_, v_v_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_toSignature_4297_; lean_object* v_value_4298_; uint8_t v_recursive_4299_; lean_object* v_inlineAttr_x3f_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4370_; 
v_toSignature_4297_ = lean_ctor_get(v_decl_4290_, 0);
v_value_4298_ = lean_ctor_get(v_decl_4290_, 1);
v_recursive_4299_ = lean_ctor_get_uint8(v_decl_4290_, sizeof(void*)*3);
v_inlineAttr_x3f_4300_ = lean_ctor_get(v_decl_4290_, 2);
v_isSharedCheck_4370_ = !lean_is_exclusive(v_decl_4290_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4302_ = v_decl_4290_;
v_isShared_4303_ = v_isSharedCheck_4370_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_inlineAttr_x3f_4300_);
lean_inc(v_value_4298_);
lean_inc(v_toSignature_4297_);
lean_dec(v_decl_4290_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4370_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v_name_4304_; lean_object* v_type_4305_; lean_object* v_params_4306_; uint8_t v_safe_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4368_; 
v_name_4304_ = lean_ctor_get(v_toSignature_4297_, 0);
v_type_4305_ = lean_ctor_get(v_toSignature_4297_, 2);
v_params_4306_ = lean_ctor_get(v_toSignature_4297_, 3);
v_safe_4307_ = lean_ctor_get_uint8(v_toSignature_4297_, sizeof(void*)*4);
v_isSharedCheck_4368_ = !lean_is_exclusive(v_toSignature_4297_);
if (v_isSharedCheck_4368_ == 0)
{
lean_object* v_unused_4369_; 
v_unused_4369_ = lean_ctor_get(v_toSignature_4297_, 1);
lean_dec(v_unused_4369_);
v___x_4309_ = v_toSignature_4297_;
v_isShared_4310_ = v_isSharedCheck_4368_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_params_4306_);
lean_inc(v_type_4305_);
lean_inc(v_name_4304_);
lean_dec(v_toSignature_4297_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4368_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___f_4311_; lean_object* v___x_4312_; 
v___f_4311_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4312_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4305_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; size_t v_sz_4314_; size_t v___x_4315_; lean_object* v___x_4316_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v_sz_4314_ = lean_array_size(v_params_4306_);
v___x_4315_ = ((size_t)0ULL);
v___x_4316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4314_, v___x_4315_, v_params_4306_, v_a_4291_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4311_, v_value_4298_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4318_) == 0)
{
lean_object* v_a_4319_; lean_object* v___x_4320_; lean_object* v___x_4322_; 
v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v___x_4318_, 1);
v___x_4320_ = lean_box(0);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 3, v_a_4317_);
lean_ctor_set(v___x_4309_, 2, v_a_4313_);
lean_ctor_set(v___x_4309_, 1, v___x_4320_);
v___x_4322_ = v___x_4309_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_name_4304_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4343_, 2, v_a_4313_);
lean_ctor_set(v_reuseFailAlloc_4343_, 3, v_a_4317_);
lean_ctor_set_uint8(v_reuseFailAlloc_4343_, sizeof(void*)*4, v_safe_4307_);
v___x_4322_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4324_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 1, v_a_4319_);
lean_ctor_set(v___x_4302_, 0, v___x_4322_);
v___x_4324_ = v___x_4302_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4322_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v_a_4319_);
lean_ctor_set(v_reuseFailAlloc_4342_, 2, v_inlineAttr_x3f_4300_);
lean_ctor_set_uint8(v_reuseFailAlloc_4342_, sizeof(void*)*3, v_recursive_4299_);
v___x_4324_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
lean_object* v___x_4325_; 
lean_inc_ref(v___x_4324_);
v___x_4325_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4324_, v_a_4295_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4332_ == 0)
{
lean_object* v_unused_4333_; 
v_unused_4333_ = lean_ctor_get(v___x_4325_, 0);
lean_dec(v_unused_4333_);
v___x_4327_ = v___x_4325_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_dec(v___x_4325_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4324_);
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4324_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
else
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4341_; 
lean_dec_ref(v___x_4324_);
v_a_4334_ = lean_ctor_get(v___x_4325_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4325_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4336_ = v___x_4325_;
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4325_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4341_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4339_; 
if (v_isShared_4337_ == 0)
{
v___x_4339_ = v___x_4336_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_a_4317_);
lean_dec(v_a_4313_);
lean_del_object(v___x_4309_);
lean_dec(v_name_4304_);
lean_del_object(v___x_4302_);
lean_dec(v_inlineAttr_x3f_4300_);
v_a_4344_ = lean_ctor_get(v___x_4318_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4318_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4318_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4318_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
else
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4359_; 
lean_dec(v_a_4313_);
lean_del_object(v___x_4309_);
lean_dec(v_name_4304_);
lean_del_object(v___x_4302_);
lean_dec(v_inlineAttr_x3f_4300_);
lean_dec_ref(v_value_4298_);
v_a_4352_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4359_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4359_ == 0)
{
v___x_4354_ = v___x_4316_;
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4316_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4359_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4357_; 
if (v_isShared_4355_ == 0)
{
v___x_4357_ = v___x_4354_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
v___x_4357_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
return v___x_4357_;
}
}
}
}
else
{
lean_object* v_a_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4367_; 
lean_del_object(v___x_4309_);
lean_dec_ref(v_params_4306_);
lean_dec(v_name_4304_);
lean_del_object(v___x_4302_);
lean_dec(v_inlineAttr_x3f_4300_);
lean_dec_ref(v_value_4298_);
v_a_4360_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4362_ = v___x_4312_;
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_a_4360_);
lean_dec(v___x_4312_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4367_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4365_; 
if (v_isShared_4363_ == 0)
{
v___x_4365_ = v___x_4362_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4385_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4386_ = lean_st_mk_ref(v___x_4385_);
v___x_4387_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4379_, v___x_4386_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4396_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4390_ = v___x_4387_;
v_isShared_4391_ = v_isSharedCheck_4396_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4387_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4396_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4392_ = lean_st_ref_get(v___x_4386_);
lean_dec(v___x_4386_);
lean_dec(v___x_4392_);
if (v_isShared_4391_ == 0)
{
v___x_4394_ = v___x_4390_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4388_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
else
{
lean_dec(v___x_4386_);
return v___x_4387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v_res_4403_; 
v_res_4403_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_a_4401_);
lean_dec_ref(v_a_4400_);
lean_dec(v_a_4399_);
lean_dec_ref(v_a_4398_);
return v_res_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4404_, size_t v_i_4405_, lean_object* v_bs_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
uint8_t v___x_4412_; 
v___x_4412_ = lean_usize_dec_lt(v_i_4405_, v_sz_4404_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4413_, 0, v_bs_4406_);
return v___x_4413_;
}
else
{
lean_object* v_v_4414_; lean_object* v___x_4415_; lean_object* v_bs_x27_4416_; lean_object* v___x_4417_; 
v_v_4414_ = lean_array_uget(v_bs_4406_, v_i_4405_);
v___x_4415_ = lean_unsigned_to_nat(0u);
v_bs_x27_4416_ = lean_array_uset(v_bs_4406_, v_i_4405_, v___x_4415_);
v___x_4417_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4414_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; size_t v___x_4419_; size_t v___x_4420_; lean_object* v___x_4421_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = ((size_t)1ULL);
v___x_4420_ = lean_usize_add(v_i_4405_, v___x_4419_);
v___x_4421_ = lean_array_uset(v_bs_x27_4416_, v_i_4405_, v_a_4418_);
v_i_4405_ = v___x_4420_;
v_bs_4406_ = v___x_4421_;
goto _start;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec_ref(v_bs_x27_4416_);
v_a_4423_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4417_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4417_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4431_, lean_object* v_i_4432_, lean_object* v_bs_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
size_t v_sz_boxed_4439_; size_t v_i_boxed_4440_; lean_object* v_res_4441_; 
v_sz_boxed_4439_ = lean_unbox_usize(v_sz_4431_);
lean_dec(v_sz_4431_);
v_i_boxed_4440_ = lean_unbox_usize(v_i_4432_);
lean_dec(v_i_4432_);
v_res_4441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4439_, v_i_boxed_4440_, v_bs_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
return v_res_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
size_t v_sz_4448_; size_t v___x_4449_; lean_object* v___x_4450_; 
v_sz_4448_ = lean_array_size(v_x_4442_);
v___x_4449_ = ((size_t)0ULL);
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4448_, v___x_4449_, v_x_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
return v___x_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
lean_object* v_res_4457_; 
v_res_4457_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
return v_res_4457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4540_; uint8_t v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4540_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4541_ = 1;
v___x_4542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4543_ = l_Lean_registerTraceClass(v___x_4540_, v___x_4541_, v___x_4542_);
return v___x_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4545_;
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
