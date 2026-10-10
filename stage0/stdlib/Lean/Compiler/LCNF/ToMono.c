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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(130, 78, 106, 49, 240, 167, 66, 80)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2;
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(lean_object* v_a_50_, lean_object* v_x_51_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_50_ = stack[0].m_obj;
lean_object* v_x_51_ = stack[1].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_50_, v_x_51_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg___boxed(lean_object* v_a_58_, lean_object* v_x_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_58_, v_x_59_);
lean_dec(v_x_59_);
lean_dec(v_a_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(lean_object* v_m_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
lean_object* v_size_65_; lean_object* v_buckets_66_; lean_object* v___x_67_; uint64_t v___x_68_; uint64_t v___x_69_; uint64_t v___x_70_; uint64_t v_fold_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; size_t v___x_78_; size_t v___x_79_; lean_object* v_bkt_80_; uint8_t v___x_81_; 
v_size_65_ = lean_ctor_get(v_m_62_, 0);
v_buckets_66_ = lean_ctor_get(v_m_62_, 1);
v___x_67_ = lean_array_get_size(v_buckets_66_);
v___x_68_ = l_Lean_instHashableFVarId_hash(v_a_63_);
v___x_69_ = 32ULL;
v___x_70_ = lean_uint64_shift_right(v___x_68_, v___x_69_);
v_fold_71_ = lean_uint64_xor(v___x_68_, v___x_70_);
v___x_72_ = 16ULL;
v___x_73_ = lean_uint64_shift_right(v_fold_71_, v___x_72_);
v___x_74_ = lean_uint64_xor(v_fold_71_, v___x_73_);
v___x_75_ = lean_uint64_to_usize(v___x_74_);
v___x_76_ = lean_usize_of_nat(v___x_67_);
v___x_77_ = ((size_t)1ULL);
v___x_78_ = lean_usize_sub(v___x_76_, v___x_77_);
v___x_79_ = lean_usize_land(v___x_75_, v___x_78_);
v_bkt_80_ = lean_array_uget_borrowed(v_buckets_66_, v___x_79_);
v___x_81_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_63_, v_bkt_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_buckets_66_);
lean_inc(v_size_65_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_m_62_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; 
v_unused_103_ = lean_ctor_get(v_m_62_, 1);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_m_62_, 0);
lean_dec(v_unused_104_);
v___x_83_ = v_m_62_;
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_m_62_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_102_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_size_x27_86_; lean_object* v___x_87_; lean_object* v_buckets_x27_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v_size_x27_86_ = lean_nat_add(v_size_65_, v___x_85_);
lean_dec(v_size_65_);
lean_inc(v_bkt_80_);
v___x_87_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_87_, 0, v_a_63_);
lean_ctor_set(v___x_87_, 1, v_b_64_);
lean_ctor_set(v___x_87_, 2, v_bkt_80_);
v_buckets_x27_88_ = lean_array_uset(v_buckets_66_, v___x_79_, v___x_87_);
v___x_89_ = lean_unsigned_to_nat(4u);
v___x_90_ = lean_nat_mul(v_size_x27_86_, v___x_89_);
v___x_91_ = lean_unsigned_to_nat(3u);
v___x_92_ = lean_nat_div(v___x_90_, v___x_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_array_get_size(v_buckets_x27_88_);
v___x_94_ = lean_nat_dec_le(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
if (v___x_94_ == 0)
{
lean_object* v_val_95_; lean_object* v___x_97_; 
v_val_95_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(v_buckets_x27_88_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_val_95_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_97_ = v___x_83_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_val_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_100_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_buckets_x27_88_);
lean_ctor_set(v___x_83_, 0, v_size_x27_86_);
v___x_100_ = v___x_83_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_size_x27_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_buckets_x27_88_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
else
{
lean_dec(v_b_64_);
lean_dec(v_a_63_);
return v_m_62_;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg(lean_object* v_param_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_fvarId_111_; lean_object* v_type_112_; lean_object* v___y_114_; lean_object* v___y_115_; lean_object* v___y_116_; uint8_t v___x_129_; 
v_fvarId_111_ = lean_ctor_get(v_param_105_, 0);
v_type_112_ = lean_ctor_get(v_param_105_, 2);
lean_inc_ref(v_type_112_);
v___x_129_ = l_Lean_Compiler_LCNF_isTypeFormerType(v_type_112_);
if (v___x_129_ == 0)
{
v___y_114_ = v_a_107_;
v___y_115_ = v_a_108_;
v___y_116_ = v_a_109_;
goto v___jp_113_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_st_ref_take(v_a_106_);
v___x_131_ = lean_box(0);
lean_inc(v_fvarId_111_);
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v___x_130_, v_fvarId_111_, v___x_131_);
v___x_133_ = lean_st_ref_put(v_a_106_, v___x_132_);
v___y_114_ = v_a_107_;
v___y_115_ = v_a_108_;
v___y_116_ = v_a_109_;
goto v___jp_113_;
}
v___jp_113_:
{
lean_object* v___x_117_; 
lean_inc_ref(v_type_112_);
v___x_117_ = l_Lean_Compiler_LCNF_toMonoType(v_type_112_, v___y_115_, v___y_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; uint8_t v___x_119_; lean_object* v___x_120_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
v___x_119_ = 0;
v___x_120_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v___x_119_, v_param_105_, v_a_118_, v___y_114_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
lean_dec_ref(v_param_105_);
v_a_121_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v___x_117_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_toMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_param_105_ = stack[0].m_obj;
lean_object* v_a_106_ = stack[1].m_obj;
lean_object* v_a_107_ = stack[2].m_obj;
lean_object* v_a_108_ = stack[3].m_obj;
lean_object* v_a_109_ = stack[4].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___redArg___boxed(lean_object* v_param_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec(v_a_136_);
return v_res_141_;
}
}
lean_object* l_Lean_Compiler_LCNF_Param_toMono(lean_object* v_param_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_param_142_, v_a_143_, v_a_145_, v_a_146_, v_a_147_);
return v___x_149_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Param_toMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_param_142_ = stack[0].m_obj;
lean_object* v_a_143_ = stack[1].m_obj;
lean_object* v_a_144_ = stack[2].m_obj;
lean_object* v_a_145_ = stack[3].m_obj;
lean_object* v_a_146_ = stack[4].m_obj;
lean_object* v_a_147_ = stack[5].m_obj;
lean_object* v_res_150_;
v_res_150_ = l_Lean_Compiler_LCNF_Param_toMono(v_param_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_);
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_toMono___boxed(lean_object* v_param_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Compiler_LCNF_Param_toMono(v_param_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0(lean_object* v_00_u03b2_159_, lean_object* v_m_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0___redArg(v_m_160_, v_a_161_, v_b_162_);
return v___x_163_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_object* v_00_u03b2_164_, lean_object* v_a_165_, lean_object* v_x_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_165_, v_x_166_);
return v___x_167_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_165_ = stack[1].m_obj;
lean_object* v_x_166_ = stack[2].m_obj;
uint8_t v_res_168_;
v_res_168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(lean_box(0), v_a_165_, v_x_166_);
stack->m_num = v_res_168_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___boxed(lean_object* v_00_u03b2_169_, lean_object* v_a_170_, lean_object* v_x_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0(v_00_u03b2_169_, v_a_170_, v_x_171_);
lean_dec(v_x_171_);
lean_dec(v_a_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1(lean_object* v_00_u03b2_174_, lean_object* v_data_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1___redArg(v_data_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_177_, lean_object* v_i_178_, lean_object* v_source_179_, lean_object* v_target_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2___redArg(v_i_178_, v_source_179_, v_target_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__1_spec__2_spec__3___redArg(v_x_183_, v_x_184_);
return v___x_185_;
}
}
lean_object* l_Lean_Compiler_LCNF_argToMono___redArg(lean_object* v_arg_188_, lean_object* v_a_189_){
_start:
{
if (lean_obj_tag(v_arg_188_) == 1)
{
lean_object* v_fvarId_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_fvarId_191_ = lean_ctor_get(v_arg_188_, 0);
v___x_192_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_193_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
v___x_194_ = lean_st_ref_get(v_a_189_);
lean_inc(v_fvarId_191_);
v___x_195_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_192_, v___x_193_, v___x_194_, v_fvarId_191_);
lean_dec(v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_arg_188_);
return v___x_196_;
}
else
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_isSharedCheck_204_ = !lean_is_exclusive(v_arg_188_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v_arg_188_, 0);
lean_dec(v_unused_205_);
v___x_198_ = v_arg_188_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_dec(v_arg_188_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_box(0);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 0);
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec(v_arg_188_);
v___x_206_ = lean_box(0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_argToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_188_ = stack[0].m_obj;
lean_object* v_a_189_ = stack[1].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_Compiler_LCNF_argToMono___redArg(v_arg_188_, v_a_189_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___redArg___boxed(lean_object* v_arg_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_Compiler_LCNF_argToMono___redArg(v_arg_209_, v_a_210_);
lean_dec(v_a_210_);
return v_res_212_;
}
}
lean_object* l_Lean_Compiler_LCNF_argToMono(lean_object* v_arg_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
if (lean_obj_tag(v_arg_213_) == 1)
{
lean_object* v_fvarId_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v_fvarId_220_ = lean_ctor_get(v_arg_213_, 0);
v___x_221_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__0));
v___x_222_ = ((lean_object*)(l_Lean_Compiler_LCNF_argToMono___redArg___closed__1));
v___x_223_ = lean_st_ref_get(v_a_214_);
lean_inc(v_fvarId_220_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___x_221_, v___x_222_, v___x_223_, v_fvarId_220_);
lean_dec(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v_arg_213_);
return v___x_225_;
}
else
{
lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_isSharedCheck_233_ = !lean_is_exclusive(v_arg_213_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_arg_213_, 0);
lean_dec(v_unused_234_);
v___x_227_ = v_arg_213_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_dec(v_arg_213_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_box(0);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 0);
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v_arg_213_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_argToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_213_ = stack[0].m_obj;
lean_object* v_a_214_ = stack[1].m_obj;
lean_object* v_a_215_ = stack[2].m_obj;
lean_object* v_a_216_ = stack[3].m_obj;
lean_object* v_a_217_ = stack[4].m_obj;
lean_object* v_a_218_ = stack[5].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_Compiler_LCNF_argToMono(v_arg_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argToMono___boxed(lean_object* v_arg_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Compiler_LCNF_argToMono(v_arg_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
return v_res_245_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_buckets_248_; lean_object* v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v_fold_253_; uint64_t v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_buckets_248_ = lean_ctor_get(v_m_246_, 1);
v___x_249_ = lean_array_get_size(v_buckets_248_);
v___x_250_ = l_Lean_instHashableFVarId_hash(v_a_247_);
v___x_251_ = 32ULL;
v___x_252_ = lean_uint64_shift_right(v___x_250_, v___x_251_);
v_fold_253_ = lean_uint64_xor(v___x_250_, v___x_252_);
v___x_254_ = 16ULL;
v___x_255_ = lean_uint64_shift_right(v_fold_253_, v___x_254_);
v___x_256_ = lean_uint64_xor(v_fold_253_, v___x_255_);
v___x_257_ = lean_uint64_to_usize(v___x_256_);
v___x_258_ = lean_usize_of_nat(v___x_249_);
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_sub(v___x_258_, v___x_259_);
v___x_261_ = lean_usize_land(v___x_257_, v___x_260_);
v___x_262_ = lean_array_uget_borrowed(v_buckets_248_, v___x_261_);
v___x_263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_Param_toMono_spec__0_spec__0___redArg(v_a_247_, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_246_ = stack[0].m_obj;
lean_object* v_a_247_ = stack[1].m_obj;
uint8_t v_res_264_;
v_res_264_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_246_, v_a_247_);
stack->m_num = v_res_264_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg___boxed(lean_object* v_m_265_, lean_object* v_a_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_m_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(lean_object* v_as_269_, size_t v_sz_270_, size_t v_i_271_, lean_object* v_b_272_, lean_object* v___y_273_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lean_usize_dec_lt(v_i_271_, v_sz_270_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v_b_272_);
return v___x_276_;
}
else
{
lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_318_; 
v_fst_277_ = lean_ctor_get(v_b_272_, 0);
v_snd_278_ = lean_ctor_get(v_b_272_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_b_272_);
if (v_isSharedCheck_318_ == 0)
{
v___x_280_ = v_b_272_;
v_isShared_281_ = v_isSharedCheck_318_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
lean_dec(v_b_272_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_318_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_monoArg_283_; lean_object* v_remainingType_284_; lean_object* v_a_292_; lean_object* v___y_294_; 
v_a_292_ = lean_array_uget_borrowed(v_as_269_, v_i_271_);
if (lean_obj_tag(v_fst_277_) == 1)
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_317_; 
v_val_301_ = lean_ctor_get(v_fst_277_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_fst_277_);
if (v_isSharedCheck_317_ == 0)
{
v___x_303_ = v_fst_277_;
v_isShared_304_ = v_isSharedCheck_317_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v_fst_277_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_317_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
if (lean_obj_tag(v_val_301_) == 7)
{
lean_object* v_binderType_305_; lean_object* v_body_306_; lean_object* v___x_308_; 
v_binderType_305_ = lean_ctor_get(v_val_301_, 1);
lean_inc_ref(v_binderType_305_);
v_body_306_ = lean_ctor_get(v_val_301_, 2);
lean_inc_ref(v_body_306_);
lean_dec_ref_known(v_val_301_, 3);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v_body_306_);
v___x_308_ = v___x_303_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_body_306_);
v___x_308_ = v_reuseFailAlloc_316_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
uint8_t v___x_309_; 
v___x_309_ = l_Lean_Expr_isErased(v_binderType_305_);
lean_dec_ref(v_binderType_305_);
if (v___x_309_ == 0)
{
if (lean_obj_tag(v_a_292_) == 1)
{
lean_object* v_fvarId_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_fvarId_310_ = lean_ctor_get(v_a_292_, 0);
v___x_311_ = lean_st_ref_get(v___y_273_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_311_, v_fvarId_310_);
lean_dec(v___x_311_);
if (v___x_312_ == 0)
{
lean_inc_ref(v_a_292_);
v_monoArg_283_ = v_a_292_;
v_remainingType_284_ = v___x_308_;
goto v___jp_282_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_box(0);
v_monoArg_283_ = v___x_313_;
v_remainingType_284_ = v___x_308_;
goto v___jp_282_;
}
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_box(0);
v_monoArg_283_ = v___x_314_;
v_remainingType_284_ = v___x_308_;
goto v___jp_282_;
}
}
else
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
v_monoArg_283_ = v___x_315_;
v_remainingType_284_ = v___x_308_;
goto v___jp_282_;
}
}
}
else
{
lean_del_object(v___x_303_);
lean_dec(v_val_301_);
v___y_294_ = v___y_273_;
goto v___jp_293_;
}
}
}
else
{
lean_dec(v_fst_277_);
v___y_294_ = v___y_273_;
goto v___jp_293_;
}
v___jp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = lean_array_push(v_snd_278_, v_monoArg_283_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_285_);
lean_ctor_set(v___x_280_, 0, v_remainingType_284_);
v___x_287_ = v___x_280_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_remainingType_284_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_291_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
size_t v___x_288_; size_t v___x_289_; 
v___x_288_ = ((size_t)1ULL);
v___x_289_ = lean_usize_add(v_i_271_, v___x_288_);
v_i_271_ = v___x_289_;
v_b_272_ = v___x_287_;
goto _start;
}
}
v___jp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = lean_box(0);
if (lean_obj_tag(v_a_292_) == 1)
{
lean_object* v_fvarId_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_fvarId_296_ = lean_ctor_get(v_a_292_, 0);
v___x_297_ = lean_st_ref_get(v___y_294_);
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_297_, v_fvarId_296_);
lean_dec(v___x_297_);
if (v___x_298_ == 0)
{
lean_inc_ref(v_a_292_);
v_monoArg_283_ = v_a_292_;
v_remainingType_284_ = v___x_295_;
goto v___jp_282_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = lean_box(0);
v_monoArg_283_ = v___x_299_;
v_remainingType_284_ = v___x_295_;
goto v___jp_282_;
}
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
v_monoArg_283_ = v___x_300_;
v_remainingType_284_ = v___x_295_;
goto v___jp_282_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_269_ = stack[0].m_obj;
size_t v_sz_270_ = stack[1].m_num;
size_t v_i_271_ = stack[2].m_num;
lean_object* v_b_272_ = stack[3].m_obj;
lean_object* v___y_273_ = stack[4].m_obj;
lean_object* v_res_319_;
v_res_319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_269_, v_sz_270_, v_i_271_, v_b_272_, v___y_273_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg___boxed(lean_object* v_as_320_, lean_object* v_sz_321_, lean_object* v_i_322_, lean_object* v_b_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
size_t v_sz_boxed_326_; size_t v_i_boxed_327_; lean_object* v_res_328_; 
v_sz_boxed_326_ = lean_unbox_usize(v_sz_321_);
lean_dec(v_sz_321_);
v_i_boxed_327_ = lean_unbox_usize(v_i_322_);
lean_dec(v_i_322_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_320_, v_sz_boxed_326_, v_i_boxed_327_, v_b_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v_as_320_);
return v_res_328_;
}
}
lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType(lean_object* v_args_329_, lean_object* v_type_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_remainingType_337_; lean_object* v___x_338_; lean_object* v_result_339_; lean_object* v___x_340_; size_t v_sz_341_; size_t v___x_342_; lean_object* v___x_343_; 
v_remainingType_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_remainingType_337_, 0, v_type_330_);
v___x_338_ = lean_array_get_size(v_args_329_);
v_result_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v_remainingType_337_);
lean_ctor_set(v___x_340_, 1, v_result_339_);
v_sz_341_ = lean_array_size(v_args_329_);
v___x_342_ = ((size_t)0ULL);
v___x_343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_args_329_, v_sz_341_, v___x_342_, v___x_340_, v_a_331_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_352_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_352_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_snd_348_; lean_object* v___x_350_; 
v_snd_348_ = lean_ctor_get(v_a_344_, 1);
lean_inc(v_snd_348_);
lean_dec(v_a_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_snd_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_snd_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_343_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_343_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_argsToMonoWithFnType_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_329_ = stack[0].m_obj;
lean_object* v_type_330_ = stack[1].m_obj;
lean_object* v_a_331_ = stack[2].m_obj;
lean_object* v_a_332_ = stack[3].m_obj;
lean_object* v_a_333_ = stack[4].m_obj;
lean_object* v_a_334_ = stack[5].m_obj;
lean_object* v_a_335_ = stack[6].m_obj;
lean_object* v_res_361_;
v_res_361_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_329_, v_type_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_argsToMonoWithFnType___boxed(lean_object* v_args_362_, lean_object* v_type_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_362_, v_type_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_args_362_);
return v_res_370_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(lean_object* v_00_u03b2_371_, lean_object* v_m_372_, lean_object* v_a_373_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v_m_372_, v_a_373_);
return v___x_374_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_372_ = stack[1].m_obj;
lean_object* v_a_373_ = stack[2].m_obj;
uint8_t v_res_375_;
v_res_375_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(lean_box(0), v_m_372_, v_a_373_);
stack->m_num = v_res_375_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___boxed(lean_object* v_00_u03b2_376_, lean_object* v_m_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0(v_00_u03b2_376_, v_m_377_, v_a_378_);
lean_dec(v_a_378_);
lean_dec_ref(v_m_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(lean_object* v_as_381_, size_t v_sz_382_, size_t v_i_383_, lean_object* v_b_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___redArg(v_as_381_, v_sz_382_, v_i_383_, v_b_384_, v___y_385_);
return v___x_391_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_381_ = stack[0].m_obj;
size_t v_sz_382_ = stack[1].m_num;
size_t v_i_383_ = stack[2].m_num;
lean_object* v_b_384_ = stack[3].m_obj;
lean_object* v___y_385_ = stack[4].m_obj;
lean_object* v___y_386_ = stack[5].m_obj;
lean_object* v___y_387_ = stack[6].m_obj;
lean_object* v___y_388_ = stack[7].m_obj;
lean_object* v___y_389_ = stack[8].m_obj;
lean_object* v_res_392_;
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(v_as_381_, v_sz_382_, v_i_383_, v_b_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1___boxed(lean_object* v_as_393_, lean_object* v_sz_394_, lean_object* v_i_395_, lean_object* v_b_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
size_t v_sz_boxed_403_; size_t v_i_boxed_404_; lean_object* v_res_405_; 
v_sz_boxed_403_ = lean_unbox_usize(v_sz_394_);
lean_dec(v_sz_394_);
v_i_boxed_404_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_res_405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__1(v_as_393_, v_sz_boxed_403_, v_i_boxed_404_, v_b_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v_as_393_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_array_408_; lean_object* v_start_409_; lean_object* v_stop_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_423_; 
v_array_408_ = lean_ctor_get(v_a_406_, 0);
v_start_409_ = lean_ctor_get(v_a_406_, 1);
v_stop_410_ = lean_ctor_get(v_a_406_, 2);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_423_ == 0)
{
v___x_412_ = v_a_406_;
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_stop_410_);
lean_inc(v_start_409_);
lean_inc(v_array_408_);
lean_dec(v_a_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___x_414_; 
v___x_414_ = lean_nat_dec_lt(v_start_409_, v_stop_410_);
if (v___x_414_ == 0)
{
lean_del_object(v___x_412_);
lean_dec(v_stop_410_);
lean_dec(v_start_409_);
lean_dec_ref(v_array_408_);
return v_b_407_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_start_409_, v___x_415_);
lean_inc_ref(v_array_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_416_);
v___x_418_ = v___x_412_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_array_408_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_stop_410_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_array_fget(v_array_408_, v_start_409_);
lean_dec(v_start_409_);
lean_dec_ref(v_array_408_);
v___x_420_ = lean_array_push(v_b_407_, v___x_419_);
v_a_406_ = v___x_418_;
v_b_407_ = v___x_420_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(size_t v_sz_424_, size_t v_i_425_, lean_object* v_bs_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_bs_426_);
return v___x_430_;
}
else
{
lean_object* v_v_431_; lean_object* v___x_432_; lean_object* v_bs_x27_433_; lean_object* v_a_435_; 
v_v_431_ = lean_array_uget(v_bs_426_, v_i_425_);
v___x_432_ = lean_unsigned_to_nat(0u);
v_bs_x27_433_ = lean_array_uset(v_bs_426_, v_i_425_, v___x_432_);
if (lean_obj_tag(v_v_431_) == 1)
{
lean_object* v_fvarId_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_fvarId_440_ = lean_ctor_get(v_v_431_, 0);
v___x_441_ = lean_st_ref_get(v___y_427_);
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_441_, v_fvarId_440_);
lean_dec(v___x_441_);
if (v___x_442_ == 0)
{
v_a_435_ = v_v_431_;
goto v___jp_434_;
}
else
{
lean_object* v___x_443_; 
lean_dec_ref_known(v_v_431_, 1);
v___x_443_ = lean_box(0);
v_a_435_ = v___x_443_;
goto v___jp_434_;
}
}
else
{
lean_object* v___x_444_; 
lean_dec(v_v_431_);
v___x_444_ = lean_box(0);
v_a_435_ = v___x_444_;
goto v___jp_434_;
}
v___jp_434_:
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_425_, v___x_436_);
v___x_438_ = lean_array_uset(v_bs_x27_433_, v_i_425_, v_a_435_);
v_i_425_ = v___x_437_;
v_bs_426_ = v___x_438_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_424_ = stack[0].m_num;
size_t v_i_425_ = stack[1].m_num;
lean_object* v_bs_426_ = stack[2].m_obj;
lean_object* v___y_427_ = stack[3].m_obj;
lean_object* v_res_445_;
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_424_, v_i_425_, v_bs_426_, v___y_427_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg___boxed(lean_object* v_sz_446_, lean_object* v_i_447_, lean_object* v_bs_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
size_t v_sz_boxed_451_; size_t v_i_boxed_452_; lean_object* v_res_453_; 
v_sz_boxed_451_ = lean_unbox_usize(v_sz_446_);
lean_dec(v_sz_446_);
v_i_boxed_452_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_boxed_451_, v_i_boxed_452_, v_bs_448_, v___y_449_);
lean_dec(v___y_449_);
return v_res_453_;
}
}
lean_object* l_Lean_Compiler_LCNF_ctorAppToMono(lean_object* v_ctorInfo_456_, lean_object* v_args_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_toConstantVal_464_; lean_object* v_numParams_465_; lean_object* v___x_466_; lean_object* v_argsNewParams_467_; lean_object* v_lower_469_; lean_object* v_upper_470_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_toConstantVal_464_ = lean_ctor_get(v_ctorInfo_456_, 0);
lean_inc_ref(v_toConstantVal_464_);
v_numParams_465_ = lean_ctor_get(v_ctorInfo_456_, 3);
lean_inc_n(v_numParams_465_, 2);
lean_dec_ref(v_ctorInfo_456_);
v___x_466_ = lean_box(0);
v_argsNewParams_467_ = lean_mk_array(v_numParams_465_, v___x_466_);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_array_get_size(v_args_457_);
v___x_507_ = lean_nat_dec_le(v_numParams_465_, v___x_505_);
if (v___x_507_ == 0)
{
v_lower_469_ = v_numParams_465_;
v_upper_470_ = v___x_506_;
goto v___jp_468_;
}
else
{
lean_dec(v_numParams_465_);
v_lower_469_ = v___x_505_;
v_upper_470_ = v___x_506_;
goto v___jp_468_;
}
v___jp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; size_t v_sz_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_471_ = l_Array_toSubarray___redArg(v_args_457_, v_lower_469_, v_upper_470_);
v___x_472_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_473_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v___x_471_, v___x_472_);
v_sz_474_ = lean_array_size(v___x_473_);
v___x_475_ = ((size_t)0ULL);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_474_, v___x_475_, v___x_473_, v_a_458_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_496_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_496_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_496_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_496_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_name_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_493_; 
v_name_481_ = lean_ctor_get(v_toConstantVal_464_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_toConstantVal_464_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; lean_object* v_unused_495_; 
v_unused_494_ = lean_ctor_get(v_toConstantVal_464_, 2);
lean_dec(v_unused_494_);
v_unused_495_ = lean_ctor_get(v_toConstantVal_464_, 1);
lean_dec(v_unused_495_);
v___x_483_ = v_toConstantVal_464_;
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_name_481_);
lean_dec(v_toConstantVal_464_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_493_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_485_ = l_Array_append___redArg(v_argsNewParams_467_, v_a_477_);
lean_dec(v_a_477_);
v___x_486_ = lean_box(0);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 3);
lean_ctor_set(v___x_483_, 2, v___x_485_);
lean_ctor_set(v___x_483_, 1, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_name_481_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_492_, 2, v___x_485_);
v___x_488_ = v_reuseFailAlloc_492_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_488_);
v___x_490_ = v___x_479_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
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
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_argsNewParams_467_);
lean_dec_ref(v_toConstantVal_464_);
v_a_497_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_476_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_476_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_ctorAppToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorInfo_456_ = stack[0].m_obj;
lean_object* v_args_457_ = stack[1].m_obj;
lean_object* v_a_458_ = stack[2].m_obj;
lean_object* v_a_459_ = stack[3].m_obj;
lean_object* v_a_460_ = stack[4].m_obj;
lean_object* v_a_461_ = stack[5].m_obj;
lean_object* v_a_462_ = stack[6].m_obj;
lean_object* v_res_508_;
v_res_508_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_ctorInfo_456_, v_args_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ctorAppToMono___boxed(lean_object* v_ctorInfo_509_, lean_object* v_args_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_ctorInfo_509_, v_args_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0(lean_object* v_inst_518_, lean_object* v_R_519_, lean_object* v_a_520_, lean_object* v_b_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__0___redArg(v_a_520_, v_b_521_);
return v___x_522_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(size_t v_sz_523_, size_t v_i_524_, lean_object* v_bs_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_523_, v_i_524_, v_bs_525_, v___y_526_);
return v___x_532_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_523_ = stack[0].m_num;
size_t v_i_524_ = stack[1].m_num;
lean_object* v_bs_525_ = stack[2].m_obj;
lean_object* v___y_526_ = stack[3].m_obj;
lean_object* v___y_527_ = stack[4].m_obj;
lean_object* v___y_528_ = stack[5].m_obj;
lean_object* v___y_529_ = stack[6].m_obj;
lean_object* v___y_530_ = stack[7].m_obj;
lean_object* v_res_533_;
v_res_533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(v_sz_523_, v_i_524_, v_bs_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___boxed(lean_object* v_sz_534_, lean_object* v_i_535_, lean_object* v_bs_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v_i_boxed_544_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1(v_sz_boxed_543_, v_i_boxed_544_, v_bs_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
return v_res_545_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0(void){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_instMonadEIO___redArg();
return v___x_546_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5(void){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Compiler_LCNF_instInhabitedLetValue_default___redArg();
return v___x_551_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_toApplicative_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_623_; 
v___x_559_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_560_ = l_StateRefT_x27_instMonad___redArg(v___x_559_);
v_toApplicative_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v___x_560_, 1);
lean_dec(v_unused_624_);
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_623_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_toApplicative_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_623_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_toFunctor_565_; lean_object* v_toSeq_566_; lean_object* v_toSeqLeft_567_; lean_object* v_toSeqRight_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_621_; 
v_toFunctor_565_ = lean_ctor_get(v_toApplicative_561_, 0);
v_toSeq_566_ = lean_ctor_get(v_toApplicative_561_, 2);
v_toSeqLeft_567_ = lean_ctor_get(v_toApplicative_561_, 3);
v_toSeqRight_568_ = lean_ctor_get(v_toApplicative_561_, 4);
v_isSharedCheck_621_ = !lean_is_exclusive(v_toApplicative_561_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_toApplicative_561_, 1);
lean_dec(v_unused_622_);
v___x_570_ = v_toApplicative_561_;
v_isShared_571_ = v_isSharedCheck_621_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_toSeqRight_568_);
lean_inc(v_toSeqLeft_567_);
lean_inc(v_toSeq_566_);
lean_inc(v_toFunctor_565_);
lean_dec(v_toApplicative_561_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_621_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___x_581_; 
v___f_572_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_573_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_565_);
v___f_574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_574_, 0, v_toFunctor_565_);
v___f_575_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_575_, 0, v_toFunctor_565_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___f_574_);
lean_ctor_set(v___x_576_, 1, v___f_575_);
v___f_577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_577_, 0, v_toSeqRight_568_);
v___f_578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_578_, 0, v_toSeqLeft_567_);
v___f_579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_579_, 0, v_toSeq_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___f_577_);
lean_ctor_set(v___x_570_, 3, v___f_578_);
lean_ctor_set(v___x_570_, 2, v___f_579_);
lean_ctor_set(v___x_570_, 1, v___f_572_);
lean_ctor_set(v___x_570_, 0, v___x_576_);
v___x_581_ = v___x_570_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___f_572_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___f_579_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v___f_578_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v___f_577_);
v___x_581_ = v_reuseFailAlloc_620_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___f_573_);
lean_ctor_set(v___x_563_, 0, v___x_581_);
v___x_583_ = v___x_563_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___f_573_);
v___x_583_ = v_reuseFailAlloc_619_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v_toApplicative_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_617_; 
v___x_584_ = l_StateRefT_x27_instMonad___redArg(v___x_583_);
v_toApplicative_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_584_, 1);
lean_dec(v_unused_618_);
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_617_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_toApplicative_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_617_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_toFunctor_589_; lean_object* v_toSeq_590_; lean_object* v_toSeqLeft_591_; lean_object* v_toSeqRight_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_615_; 
v_toFunctor_589_ = lean_ctor_get(v_toApplicative_585_, 0);
v_toSeq_590_ = lean_ctor_get(v_toApplicative_585_, 2);
v_toSeqLeft_591_ = lean_ctor_get(v_toApplicative_585_, 3);
v_toSeqRight_592_ = lean_ctor_get(v_toApplicative_585_, 4);
v_isSharedCheck_615_ = !lean_is_exclusive(v_toApplicative_585_);
if (v_isSharedCheck_615_ == 0)
{
lean_object* v_unused_616_; 
v_unused_616_ = lean_ctor_get(v_toApplicative_585_, 1);
lean_dec(v_unused_616_);
v___x_594_ = v_toApplicative_585_;
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_toSeqRight_592_);
lean_inc(v_toSeqLeft_591_);
lean_inc(v_toSeq_590_);
lean_inc(v_toFunctor_589_);
lean_dec(v_toApplicative_585_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___f_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___x_605_; 
v___f_596_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_597_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_589_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_598_, 0, v_toFunctor_589_);
v___f_599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_599_, 0, v_toFunctor_589_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___f_598_);
lean_ctor_set(v___x_600_, 1, v___f_599_);
v___f_601_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_601_, 0, v_toSeqRight_592_);
v___f_602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_602_, 0, v_toSeqLeft_591_);
v___f_603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_603_, 0, v_toSeq_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 4, v___f_601_);
lean_ctor_set(v___x_594_, 3, v___f_602_);
lean_ctor_set(v___x_594_, 2, v___f_603_);
lean_ctor_set(v___x_594_, 1, v___f_596_);
lean_ctor_set(v___x_594_, 0, v___x_600_);
v___x_605_ = v___x_594_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___f_596_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___f_603_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v___f_602_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v___f_601_);
v___x_605_ = v_reuseFailAlloc_614_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___f_597_);
lean_ctor_set(v___x_587_, 0, v___x_605_);
v___x_607_ = v___x_587_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___f_597_);
v___x_607_ = v_reuseFailAlloc_613_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_6341__overap_611_; lean_object* v___x_612_; 
v___x_608_ = l_StateRefT_x27_instMonad___redArg(v___x_607_);
v___x_609_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__5);
v___x_610_ = l_instInhabitedOfMonad___redArg(v___x_608_, v___x_609_);
v___x_6341__overap_611_ = lean_panic_fn_borrowed(v___x_610_, v_msg_552_);
lean_dec(v___x_610_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
v___x_612_ = lean_apply_6(v___x_6341__overap_611_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, lean_box(0));
return v___x_612_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_552_ = stack[0].m_obj;
lean_object* v___y_553_ = stack[1].m_obj;
lean_object* v___y_554_ = stack[2].m_obj;
lean_object* v___y_555_ = stack[3].m_obj;
lean_object* v___y_556_ = stack[4].m_obj;
lean_object* v___y_557_ = stack[5].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___boxed(lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v_msg_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
return v_res_633_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(lean_object* v_upperBound_634_, lean_object* v_args_635_, lean_object* v_a_636_, lean_object* v_b_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_a_641_; uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_lt(v_a_636_, v_upperBound_634_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v_a_636_);
v___x_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_647_, 0, v_b_637_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_box(0);
v___x_649_ = lean_array_get_borrowed(v___x_648_, v_args_635_, v_a_636_);
if (lean_obj_tag(v___x_649_) == 1)
{
lean_object* v_fvarId_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_fvarId_650_ = lean_ctor_get(v___x_649_, 0);
v___x_651_ = lean_st_ref_get(v___y_638_);
v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_651_, v_fvarId_650_);
lean_dec(v___x_651_);
if (v___x_652_ == 0)
{
lean_inc_ref(v___x_649_);
v_a_641_ = v___x_649_;
goto v___jp_640_;
}
else
{
v_a_641_ = v___x_648_;
goto v___jp_640_;
}
}
else
{
v_a_641_ = v___x_648_;
goto v___jp_640_;
}
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_array_push(v_b_637_, v_a_641_);
v___x_643_ = lean_unsigned_to_nat(1u);
v___x_644_ = lean_nat_add(v_a_636_, v___x_643_);
lean_dec(v_a_636_);
v_a_636_ = v___x_644_;
v_b_637_ = v___x_642_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_634_ = stack[0].m_obj;
lean_object* v_args_635_ = stack[1].m_obj;
lean_object* v_a_636_ = stack[2].m_obj;
lean_object* v_b_637_ = stack[3].m_obj;
lean_object* v___y_638_ = stack[4].m_obj;
lean_object* v_res_653_;
v_res_653_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_634_, v_args_635_, v_a_636_, v_b_637_, v___y_638_);
stack->m_obj
 = v_res_653_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg___boxed(lean_object* v_upperBound_654_, lean_object* v_args_655_, lean_object* v_a_656_, lean_object* v_b_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_654_, v_args_655_, v_a_656_, v_b_657_, v___y_658_);
lean_dec(v___y_658_);
lean_dec_ref(v_args_655_);
lean_dec(v_upperBound_654_);
return v_res_660_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__13(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_683_ = lean_unsigned_to_nat(6u);
v___x_684_ = lean_unsigned_to_nat(83u);
v___x_685_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__11));
v___x_686_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_687_ = l_mkPanicMessageWithDecl(v___x_686_, v___x_685_, v___x_684_, v___x_683_, v___x_682_);
return v___x_687_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetValue_toMono(lean_object* v_e_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
switch(lean_obj_tag(v_e_692_))
{
case 2:
{
lean_object* v_typeName_699_; lean_object* v_idx_700_; lean_object* v_struct_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_typeName_699_ = lean_ctor_get(v_e_692_, 0);
v_idx_700_ = lean_ctor_get(v_e_692_, 1);
v_struct_701_ = lean_ctor_get(v_e_692_, 2);
v___x_702_ = lean_st_ref_get(v_a_693_);
v___x_703_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_702_, v_struct_701_);
lean_dec(v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; 
lean_inc(v_typeName_699_);
v___x_704_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_699_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_724_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_724_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_724_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_724_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
if (lean_obj_tag(v_a_705_) == 1)
{
lean_object* v_val_709_; lean_object* v_fieldIdx_710_; uint8_t v___x_711_; 
lean_inc(v_struct_701_);
lean_inc(v_idx_700_);
lean_dec_ref_known(v_e_692_, 3);
v_val_709_ = lean_ctor_get(v_a_705_, 0);
lean_inc(v_val_709_);
lean_dec_ref_known(v_a_705_, 1);
v_fieldIdx_710_ = lean_ctor_get(v_val_709_, 2);
lean_inc(v_fieldIdx_710_);
lean_dec(v_val_709_);
v___x_711_ = lean_nat_dec_eq(v_fieldIdx_710_, v_idx_700_);
lean_dec(v_idx_700_);
lean_dec(v_fieldIdx_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_dec(v_struct_701_);
v___x_712_ = lean_box(1);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_712_);
v___x_714_ = v___x_707_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_716_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_717_, 0, v_struct_701_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_717_);
v___x_719_ = v___x_707_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
lean_object* v___x_722_; 
lean_dec(v_a_705_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_e_692_);
v___x_722_ = v___x_707_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_e_692_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref_known(v_e_692_, 3);
v_a_725_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_704_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_704_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; 
lean_dec_ref_known(v_e_692_, 3);
v___x_733_ = lean_box(1);
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
case 3:
{
lean_object* v_declName_735_; lean_object* v_args_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_858_; 
v_declName_735_ = lean_ctor_get(v_e_692_, 0);
v_args_736_ = lean_ctor_get(v_e_692_, 2);
v_isSharedCheck_858_ = !lean_is_exclusive(v_e_692_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_e_692_, 1);
lean_dec(v_unused_859_);
v___x_738_ = v_e_692_;
v_isShared_739_ = v_isSharedCheck_858_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_args_736_);
lean_inc(v_declName_735_);
lean_dec(v_e_692_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_858_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v_args_741_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__2));
v___x_789_ = lean_name_eq(v_declName_735_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__4));
v___x_791_ = lean_name_eq(v_declName_735_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__7));
v___x_793_ = lean_name_eq(v_declName_735_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_795_ = lean_name_eq(v_declName_735_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v_env_797_; lean_object* v___x_798_; 
v___x_796_ = lean_st_ref_get(v_a_697_);
v_env_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc_ref(v_env_797_);
lean_dec(v___x_796_);
lean_inc(v_declName_735_);
v___x_798_ = l_Lean_Environment_find_x3f(v_env_797_, v_declName_735_, v___x_795_);
if (lean_obj_tag(v___x_798_) == 1)
{
lean_object* v_val_799_; 
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_798_, 1);
if (lean_obj_tag(v_val_799_) == 6)
{
lean_object* v_val_800_; lean_object* v_induct_801_; lean_object* v_numParams_802_; lean_object* v___x_803_; 
lean_del_object(v___x_738_);
lean_dec(v_declName_735_);
v_val_800_ = lean_ctor_get(v_val_799_, 0);
lean_inc_ref(v_val_800_);
lean_dec_ref_known(v_val_799_, 1);
v_induct_801_ = lean_ctor_get(v_val_800_, 1);
v_numParams_802_ = lean_ctor_get(v_val_800_, 3);
lean_inc(v_induct_801_);
v___x_803_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_induct_801_, v_a_696_, v_a_697_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
if (lean_obj_tag(v_a_804_) == 1)
{
lean_object* v_val_805_; lean_object* v_fieldIdx_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc(v_numParams_802_);
lean_dec_ref(v_val_800_);
v_val_805_ = lean_ctor_get(v_a_804_, 0);
lean_inc(v_val_805_);
lean_dec_ref_known(v_a_804_, 1);
v_fieldIdx_806_ = lean_ctor_get(v_val_805_, 2);
lean_inc(v_fieldIdx_806_);
lean_dec(v_val_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_nat_add(v_numParams_802_, v_fieldIdx_806_);
lean_dec(v_fieldIdx_806_);
lean_dec(v_numParams_802_);
v___x_809_ = lean_array_get(v___x_807_, v_args_736_, v___x_808_);
lean_dec(v___x_808_);
lean_dec_ref(v_args_736_);
v___x_810_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_809_);
lean_dec(v___x_809_);
v_e_692_ = v___x_810_;
goto _start;
}
else
{
lean_object* v___x_812_; 
lean_dec(v_a_804_);
v___x_812_ = l_Lean_Compiler_LCNF_ctorAppToMono(v_val_800_, v_args_736_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_812_;
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec_ref(v_val_800_);
lean_dec_ref(v_args_736_);
v_a_813_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_803_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_803_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
else
{
lean_dec(v_val_799_);
v___y_748_ = v_a_693_;
v___y_749_ = v_a_694_;
v___y_750_ = v_a_695_;
v___y_751_ = v_a_696_;
v___y_752_ = v_a_697_;
goto v___jp_747_;
}
}
else
{
lean_dec(v___x_798_);
v___y_748_ = v_a_693_;
v___y_749_ = v_a_694_;
v___y_750_ = v_a_695_;
v___y_751_ = v_a_696_;
v___y_752_ = v_a_697_;
goto v___jp_747_;
}
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_del_object(v___x_738_);
lean_dec_ref(v_args_736_);
lean_dec(v_declName_735_);
v___x_821_ = lean_obj_once(&l_Lean_Compiler_LCNF_LetValue_toMono___closed__13, &l_Lean_Compiler_LCNF_LetValue_toMono___closed__13_once, _init_l_Lean_Compiler_LCNF_LetValue_toMono___closed__13);
v___x_822_ = l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0(v___x_821_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_822_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_del_object(v___x_738_);
lean_dec_ref(v_args_736_);
lean_dec(v_declName_735_);
v___x_823_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
return v___x_824_;
}
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_738_);
lean_dec(v_declName_735_);
v___x_825_ = lean_box(0);
v___x_826_ = lean_unsigned_to_nat(2u);
v___x_827_ = lean_array_get_borrowed(v___x_825_, v_args_736_, v___x_826_);
if (lean_obj_tag(v___x_827_) == 1)
{
lean_object* v_fvarId_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_extraArgs_832_; lean_object* v___x_833_; 
v_fvarId_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_fvarId_828_);
v___x_829_ = lean_array_get_size(v_args_736_);
v___x_830_ = lean_unsigned_to_nat(3u);
v___x_831_ = lean_nat_sub(v___x_829_, v___x_830_);
v_extraArgs_832_ = lean_mk_empty_array_with_capacity(v___x_831_);
lean_dec(v___x_831_);
v___x_833_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v___x_829_, v_args_736_, v___x_830_, v_extraArgs_832_, v_a_693_);
lean_dec_ref(v_args_736_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_842_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_838_, 0, v_fvarId_828_);
lean_ctor_set(v___x_838_, 1, v_a_834_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_fvarId_828_);
v_a_843_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_833_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_833_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref(v_args_736_);
v___x_851_ = lean_box(1);
v___x_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
return v___x_852_;
}
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_del_object(v___x_738_);
lean_dec(v_declName_735_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_unsigned_to_nat(2u);
v___x_855_ = lean_array_get(v___x_853_, v_args_736_, v___x_854_);
lean_dec_ref(v_args_736_);
v___x_856_ = l_Lean_Compiler_LCNF_Arg_toLetValue___redArg(v___x_855_);
lean_dec(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
v___jp_740_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_box(0);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 2, v_args_741_);
lean_ctor_set(v___x_738_, 1, v___x_742_);
v___x_744_ = v___x_738_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_declName_735_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_args_741_);
v___x_744_ = v_reuseFailAlloc_746_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; 
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
return v___x_745_;
}
}
v___jp_747_:
{
lean_object* v___x_753_; 
lean_inc(v_declName_735_);
v___x_753_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_735_, v___y_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
if (lean_obj_tag(v_a_754_) == 1)
{
lean_object* v_val_755_; lean_object* v_toSignature_756_; lean_object* v_type_757_; lean_object* v___x_758_; 
v_val_755_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v_a_754_, 1);
v_toSignature_756_ = lean_ctor_get(v_val_755_, 0);
lean_inc_ref(v_toSignature_756_);
lean_dec(v_val_755_);
v_type_757_ = lean_ctor_get(v_toSignature_756_, 2);
lean_inc_ref(v_type_757_);
lean_dec_ref(v_toSignature_756_);
v___x_758_ = l_Lean_Compiler_LCNF_argsToMonoWithFnType(v_args_736_, v_type_757_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v_args_736_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v_args_741_ = v_a_759_;
goto v___jp_740_;
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_del_object(v___x_738_);
lean_dec(v_declName_735_);
v_a_760_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_758_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_758_);
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
else
{
size_t v_sz_768_; size_t v___x_769_; lean_object* v___x_770_; 
lean_dec(v_a_754_);
v_sz_768_ = lean_array_size(v_args_736_);
v___x_769_ = ((size_t)0ULL);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_768_, v___x_769_, v_args_736_, v___y_748_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v_args_741_ = v_a_771_;
goto v___jp_740_;
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_del_object(v___x_738_);
lean_dec(v_declName_735_);
v_a_772_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_770_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_770_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_del_object(v___x_738_);
lean_dec_ref(v_args_736_);
lean_dec(v_declName_735_);
v_a_780_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_753_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_753_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
case 4:
{
lean_object* v_fvarId_860_; lean_object* v_args_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_891_; 
v_fvarId_860_ = lean_ctor_get(v_e_692_, 0);
v_args_861_ = lean_ctor_get(v_e_692_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v_e_692_);
if (v_isSharedCheck_891_ == 0)
{
v___x_863_ = v_e_692_;
v_isShared_864_ = v_isSharedCheck_891_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_args_861_);
lean_inc(v_fvarId_860_);
lean_dec(v_e_692_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_891_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = lean_st_ref_get(v_a_693_);
v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_argsToMonoWithFnType_spec__0___redArg(v___x_865_, v_fvarId_860_);
lean_dec(v___x_865_);
if (v___x_866_ == 0)
{
size_t v_sz_867_; size_t v___x_868_; lean_object* v___x_869_; 
v_sz_867_ = lean_array_size(v_args_861_);
v___x_868_ = ((size_t)0ULL);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_867_, v___x_868_, v_args_861_, v_a_693_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_880_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_880_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v_a_870_);
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_fvarId_860_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_870_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_del_object(v___x_863_);
lean_dec(v_fvarId_860_);
v_a_881_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_869_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_869_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_del_object(v___x_863_);
lean_dec_ref(v_args_861_);
lean_dec(v_fvarId_860_);
v___x_889_ = lean_box(1);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
}
default: 
{
lean_object* v___x_892_; 
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v_e_692_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_toMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_692_ = stack[0].m_obj;
lean_object* v_a_693_ = stack[1].m_obj;
lean_object* v_a_694_ = stack[2].m_obj;
lean_object* v_a_695_ = stack[3].m_obj;
lean_object* v_a_696_ = stack[4].m_obj;
lean_object* v_a_697_ = stack[5].m_obj;
lean_object* v_res_893_;
v_res_893_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_toMono___boxed(lean_object* v_e_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_e_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
return v_res_901_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(lean_object* v_upperBound_902_, lean_object* v_args_903_, lean_object* v_inst_904_, lean_object* v_R_905_, lean_object* v_a_906_, lean_object* v_b_907_, lean_object* v_c_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___redArg(v_upperBound_902_, v_args_903_, v_a_906_, v_b_907_, v___y_909_);
return v___x_915_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_902_ = stack[0].m_obj;
lean_object* v_args_903_ = stack[1].m_obj;
lean_object* v_a_906_ = stack[4].m_obj;
lean_object* v_b_907_ = stack[5].m_obj;
lean_object* v___y_909_ = stack[7].m_obj;
lean_object* v___y_910_ = stack[8].m_obj;
lean_object* v___y_911_ = stack[9].m_obj;
lean_object* v___y_912_ = stack[10].m_obj;
lean_object* v___y_913_ = stack[11].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_902_, v_args_903_, lean_box(0), lean_box(0), v_a_906_, v_b_907_, lean_box(0), v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1___boxed(lean_object* v_upperBound_917_, lean_object* v_args_918_, lean_object* v_inst_919_, lean_object* v_R_920_, lean_object* v_a_921_, lean_object* v_b_922_, lean_object* v_c_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__1(v_upperBound_917_, v_args_918_, v_inst_919_, v_R_920_, v_a_921_, v_b_922_, v_c_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v_args_918_);
lean_dec(v_upperBound_917_);
return v_res_930_;
}
}
lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono(lean_object* v_decl_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_type_938_; lean_object* v_value_939_; lean_object* v___x_940_; 
v_type_938_ = lean_ctor_get(v_decl_931_, 2);
v_value_939_ = lean_ctor_get(v_decl_931_, 3);
lean_inc_ref(v_type_938_);
v___x_940_ = l_Lean_Compiler_LCNF_toMonoType(v_type_938_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
lean_inc(v_value_939_);
v___x_942_ = l_Lean_Compiler_LCNF_LetValue_toMono(v_value_939_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; uint8_t v___x_944_; lean_object* v___x_945_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = 0;
v___x_945_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_944_, v_decl_931_, v_a_941_, v_a_943_, v_a_934_);
return v___x_945_;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_a_941_);
lean_dec_ref(v_decl_931_);
v_a_946_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_942_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_942_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
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
lean_dec_ref(v_decl_931_);
v_a_954_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_940_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_940_);
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
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_toMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_931_ = stack[0].m_obj;
lean_object* v_a_932_ = stack[1].m_obj;
lean_object* v_a_933_ = stack[2].m_obj;
lean_object* v_a_934_ = stack[3].m_obj;
lean_object* v_a_935_ = stack[4].m_obj;
lean_object* v_a_936_ = stack[5].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_toMono___boxed(lean_object* v_decl_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
return v_res_970_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v_toApplicative_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1042_; 
v___x_978_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_979_ = l_StateRefT_x27_instMonad___redArg(v___x_978_);
v_toApplicative_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v___x_979_, 1);
lean_dec(v_unused_1043_);
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_1042_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_toApplicative_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1042_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_toFunctor_984_; lean_object* v_toSeq_985_; lean_object* v_toSeqLeft_986_; lean_object* v_toSeqRight_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1040_; 
v_toFunctor_984_ = lean_ctor_get(v_toApplicative_980_, 0);
v_toSeq_985_ = lean_ctor_get(v_toApplicative_980_, 2);
v_toSeqLeft_986_ = lean_ctor_get(v_toApplicative_980_, 3);
v_toSeqRight_987_ = lean_ctor_get(v_toApplicative_980_, 4);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_toApplicative_980_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_toApplicative_980_, 1);
lean_dec(v_unused_1041_);
v___x_989_ = v_toApplicative_980_;
v_isShared_990_ = v_isSharedCheck_1040_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_toSeqRight_987_);
lean_inc(v_toSeqLeft_986_);
lean_inc(v_toSeq_985_);
lean_inc(v_toFunctor_984_);
lean_dec(v_toApplicative_980_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1040_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___x_1000_; 
v___f_991_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_992_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
lean_inc_ref(v_toFunctor_984_);
v___f_993_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_993_, 0, v_toFunctor_984_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_994_, 0, v_toFunctor_984_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___f_993_);
lean_ctor_set(v___x_995_, 1, v___f_994_);
v___f_996_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_996_, 0, v_toSeqRight_987_);
v___f_997_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_997_, 0, v_toSeqLeft_986_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_998_, 0, v_toSeq_985_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 4, v___f_996_);
lean_ctor_set(v___x_989_, 3, v___f_997_);
lean_ctor_set(v___x_989_, 2, v___f_998_);
lean_ctor_set(v___x_989_, 1, v___f_991_);
lean_ctor_set(v___x_989_, 0, v___x_995_);
v___x_1000_ = v___x_989_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___f_991_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v___f_998_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v___f_997_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v___f_996_);
v___x_1000_ = v_reuseFailAlloc_1039_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___f_992_);
lean_ctor_set(v___x_982_, 0, v___x_1000_);
v___x_1002_ = v___x_982_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___f_992_);
v___x_1002_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v_toApplicative_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1036_; 
v___x_1003_ = l_StateRefT_x27_instMonad___redArg(v___x_1002_);
v_toApplicative_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___x_1003_, 1);
lean_dec(v_unused_1037_);
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1036_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_toApplicative_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1036_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_toFunctor_1008_; lean_object* v_toSeq_1009_; lean_object* v_toSeqLeft_1010_; lean_object* v_toSeqRight_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1034_; 
v_toFunctor_1008_ = lean_ctor_get(v_toApplicative_1004_, 0);
v_toSeq_1009_ = lean_ctor_get(v_toApplicative_1004_, 2);
v_toSeqLeft_1010_ = lean_ctor_get(v_toApplicative_1004_, 3);
v_toSeqRight_1011_ = lean_ctor_get(v_toApplicative_1004_, 4);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_toApplicative_1004_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_toApplicative_1004_, 1);
lean_dec(v_unused_1035_);
v___x_1013_ = v_toApplicative_1004_;
v_isShared_1014_ = v_isSharedCheck_1034_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_toSeqRight_1011_);
lean_inc(v_toSeqLeft_1010_);
lean_inc(v_toSeq_1009_);
lean_inc(v_toFunctor_1008_);
lean_dec(v_toApplicative_1004_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1034_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___x_1024_; 
v___f_1015_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1016_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1008_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toFunctor_1008_);
v___f_1018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1018_, 0, v_toFunctor_1008_);
v___x_1019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___f_1017_);
lean_ctor_set(v___x_1019_, 1, v___f_1018_);
v___f_1020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1020_, 0, v_toSeqRight_1011_);
v___f_1021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1021_, 0, v_toSeqLeft_1010_);
v___f_1022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1022_, 0, v_toSeq_1009_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 4, v___f_1020_);
lean_ctor_set(v___x_1013_, 3, v___f_1021_);
lean_ctor_set(v___x_1013_, 2, v___f_1022_);
lean_ctor_set(v___x_1013_, 1, v___f_1015_);
lean_ctor_set(v___x_1013_, 0, v___x_1019_);
v___x_1024_ = v___x_1013_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v___f_1015_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v___f_1022_);
lean_ctor_set(v_reuseFailAlloc_1033_, 3, v___f_1021_);
lean_ctor_set(v_reuseFailAlloc_1033_, 4, v___f_1020_);
v___x_1024_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v___f_1016_);
lean_ctor_set(v___x_1006_, 0, v___x_1024_);
v___x_1026_ = v___x_1006_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___f_1016_);
v___x_1026_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_4525__overap_1030_; lean_object* v___x_1031_; 
v___x_1027_ = l_StateRefT_x27_instMonad___redArg(v___x_1026_);
v___x_1028_ = lean_box(0);
v___x_1029_ = l_instInhabitedOfMonad___redArg(v___x_1027_, v___x_1028_);
v___x_4525__overap_1030_ = lean_panic_fn_borrowed(v___x_1029_, v_msg_971_);
lean_dec(v___x_1029_);
lean_inc(v___y_976_);
lean_inc_ref(v___y_975_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
v___x_1031_ = lean_apply_6(v___x_4525__overap_1030_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, lean_box(0));
return v___x_1031_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_971_ = stack[0].m_obj;
lean_object* v___y_972_ = stack[1].m_obj;
lean_object* v___y_973_ = stack[2].m_obj;
lean_object* v___y_974_ = stack[3].m_obj;
lean_object* v___y_975_ = stack[4].m_obj;
lean_object* v___y_976_ = stack[5].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0___boxed(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
return v_res_1052_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1054_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1055_ = lean_unsigned_to_nat(11u);
v___x_1056_ = lean_unsigned_to_nat(124u);
v___x_1057_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1058_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1059_ = l_mkPanicMessageWithDecl(v___x_1058_, v___x_1057_, v___x_1056_, v___x_1055_, v___x_1054_);
return v___x_1059_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(lean_object* v_upperBound_1060_, lean_object* v_a_1061_, lean_object* v_b_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_a_1070_; uint8_t v___x_1074_; 
v___x_1074_ = lean_nat_dec_lt(v_a_1061_, v_upperBound_1060_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v_a_1061_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_b_1062_);
return v___x_1075_;
}
else
{
if (lean_obj_tag(v_b_1062_) == 7)
{
lean_object* v_body_1076_; 
v_body_1076_ = lean_ctor_get(v_b_1062_, 2);
lean_inc_ref(v_body_1076_);
lean_dec_ref_known(v_b_1062_, 3);
v_a_1070_ = v_body_1076_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__1);
v___x_1078_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1077_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_dec_ref_known(v___x_1078_, 1);
v_a_1070_ = v_b_1062_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_b_1062_);
lean_dec(v_a_1061_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
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
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(1u);
v___x_1072_ = lean_nat_add(v_a_1061_, v___x_1071_);
lean_dec(v_a_1061_);
v_a_1061_ = v___x_1072_;
v_b_1062_ = v_a_1070_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1060_ = stack[0].m_obj;
lean_object* v_a_1061_ = stack[1].m_obj;
lean_object* v_b_1062_ = stack[2].m_obj;
lean_object* v___y_1063_ = stack[3].m_obj;
lean_object* v___y_1064_ = stack[4].m_obj;
lean_object* v___y_1065_ = stack[5].m_obj;
lean_object* v___y_1066_ = stack[6].m_obj;
lean_object* v___y_1067_ = stack[7].m_obj;
lean_object* v_res_1087_;
v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1060_, v_a_1061_, v_b_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
stack->m_obj
 = v_res_1087_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___boxed(lean_object* v_upperBound_1088_, lean_object* v_a_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1088_, v_a_1089_, v_b_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec(v_upperBound_1088_);
return v_res_1097_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1098_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1099_ = lean_unsigned_to_nat(11u);
v___x_1100_ = lean_unsigned_to_nat(132u);
v___x_1101_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg___closed__0));
v___x_1102_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1103_ = l_mkPanicMessageWithDecl(v___x_1102_, v___x_1101_, v___x_1100_, v___x_1099_, v___x_1098_);
return v___x_1103_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(lean_object* v_upperBound_1104_, lean_object* v_a_1105_, lean_object* v_b_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_a_1114_; uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_lt(v_a_1105_, v_upperBound_1104_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec(v_a_1105_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_b_1106_);
return v___x_1119_;
}
else
{
lean_object* v_fst_1120_; 
v_fst_1120_ = lean_ctor_get(v_b_1106_, 0);
lean_inc(v_fst_1120_);
if (lean_obj_tag(v_fst_1120_) == 7)
{
lean_object* v_snd_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1154_; 
v_snd_1121_ = lean_ctor_get(v_b_1106_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_b_1106_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_b_1106_, 0);
lean_dec(v_unused_1155_);
v___x_1123_ = v_b_1106_;
v_isShared_1124_ = v_isSharedCheck_1154_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_snd_1121_);
lean_dec(v_b_1106_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1154_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_binderName_1125_; lean_object* v_binderType_1126_; lean_object* v_body_1127_; lean_object* v___x_1128_; 
v_binderName_1125_ = lean_ctor_get(v_fst_1120_, 0);
lean_inc(v_binderName_1125_);
v_binderType_1126_ = lean_ctor_get(v_fst_1120_, 1);
lean_inc_ref(v_binderType_1126_);
v_body_1127_ = lean_ctor_get(v_fst_1120_, 2);
lean_inc_ref(v_body_1127_);
lean_dec_ref_known(v_fst_1120_, 3);
v___x_1128_ = l_Lean_Compiler_LCNF_toMonoType(v_binderType_1126_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; uint8_t v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = 0;
v___x_1131_ = 0;
v___x_1132_ = l_Lean_Compiler_LCNF_mkParam(v___x_1130_, v_binderName_1125_, v_a_1129_, v___x_1131_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = lean_array_push(v_snd_1121_, v_a_1133_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v___x_1134_);
lean_ctor_set(v___x_1123_, 0, v_body_1127_);
v___x_1136_ = v___x_1123_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_body_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
v_a_1114_ = v___x_1136_;
goto v___jp_1113_;
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec_ref(v_body_1127_);
lean_del_object(v___x_1123_);
lean_dec(v_snd_1121_);
lean_dec(v_a_1105_);
v_a_1138_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1132_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1132_);
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
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec_ref(v_body_1127_);
lean_dec(v_binderName_1125_);
lean_del_object(v___x_1123_);
lean_dec(v_snd_1121_);
lean_dec(v_a_1105_);
v_a_1146_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1128_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1128_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
else
{
lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1173_; 
v_snd_1156_ = lean_ctor_get(v_b_1106_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_b_1106_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v_b_1106_, 0);
lean_dec(v_unused_1174_);
v___x_1158_ = v_b_1106_;
v_isShared_1159_ = v_isSharedCheck_1173_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_dec(v_b_1106_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1173_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___closed__0);
v___x_1161_ = l_panic___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__0(v___x_1160_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref_known(v___x_1161_, 1);
if (v_isShared_1159_ == 0)
{
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_fst_1120_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_snd_1156_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
v_a_1114_ = v___x_1163_;
goto v___jp_1113_;
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_del_object(v___x_1158_);
lean_dec(v_snd_1156_);
lean_dec(v_fst_1120_);
lean_dec(v_a_1105_);
v_a_1165_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1161_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1161_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
}
v___jp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_a_1105_, v___x_1115_);
lean_dec(v_a_1105_);
v_a_1105_ = v___x_1116_;
v_b_1106_ = v_a_1114_;
goto _start;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1104_ = stack[0].m_obj;
lean_object* v_a_1105_ = stack[1].m_obj;
lean_object* v_b_1106_ = stack[2].m_obj;
lean_object* v___y_1107_ = stack[3].m_obj;
lean_object* v___y_1108_ = stack[4].m_obj;
lean_object* v___y_1109_ = stack[5].m_obj;
lean_object* v___y_1110_ = stack[6].m_obj;
lean_object* v___y_1111_ = stack[7].m_obj;
lean_object* v_res_1175_;
v_res_1175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1104_, v_a_1105_, v_b_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
stack->m_obj
 = v_res_1175_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg___boxed(lean_object* v_upperBound_1176_, lean_object* v_a_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1176_, v_a_1177_, v_b_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v_upperBound_1176_);
return v_res_1185_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(lean_object* v_ctorType_1186_, lean_object* v_numParams_1187_, lean_object* v_numNewFields_1188_, lean_object* v_oldFields_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_numParams_1187_, v___x_1196_, v_ctorType_1186_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = lean_array_get_size(v_oldFields_1189_);
v___x_1200_ = lean_nat_add(v___x_1199_, v_numNewFields_1188_);
v___x_1201_ = lean_mk_empty_array_with_capacity(v___x_1200_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_a_1198_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_numNewFields_1188_, v___x_1196_, v___x_1202_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_snd_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v_snd_1208_ = lean_ctor_get(v_a_1204_, 1);
lean_inc(v_snd_1208_);
lean_dec(v_a_1204_);
v___x_1209_ = l_Array_append___redArg(v_snd_1208_, v_oldFields_1189_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1209_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1203_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1203_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1197_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1197_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorType_1186_ = stack[0].m_obj;
lean_object* v_numParams_1187_ = stack[1].m_obj;
lean_object* v_numNewFields_1188_ = stack[2].m_obj;
lean_object* v_oldFields_1189_ = stack[3].m_obj;
lean_object* v_a_1190_ = stack[4].m_obj;
lean_object* v_a_1191_ = stack[5].m_obj;
lean_object* v_a_1192_ = stack[6].m_obj;
lean_object* v_a_1193_ = stack[7].m_obj;
lean_object* v_a_1194_ = stack[8].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1186_, v_numParams_1187_, v_numNewFields_1188_, v_oldFields_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields___boxed(lean_object* v_ctorType_1231_, lean_object* v_numParams_1232_, lean_object* v_numNewFields_1233_, lean_object* v_oldFields_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_ctorType_1231_, v_numParams_1232_, v_numNewFields_1233_, v_oldFields_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_oldFields_1234_);
lean_dec(v_numNewFields_1233_);
lean_dec(v_numParams_1232_);
return v_res_1241_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(lean_object* v_upperBound_1242_, lean_object* v_inst_1243_, lean_object* v_R_1244_, lean_object* v_a_1245_, lean_object* v_b_1246_, lean_object* v_c_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___redArg(v_upperBound_1242_, v_a_1245_, v_b_1246_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1242_ = stack[0].m_obj;
lean_object* v_a_1245_ = stack[3].m_obj;
lean_object* v_b_1246_ = stack[4].m_obj;
lean_object* v___y_1248_ = stack[6].m_obj;
lean_object* v___y_1249_ = stack[7].m_obj;
lean_object* v___y_1250_ = stack[8].m_obj;
lean_object* v___y_1251_ = stack[9].m_obj;
lean_object* v___y_1252_ = stack[10].m_obj;
lean_object* v_res_1255_;
v_res_1255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1242_, lean_box(0), lean_box(0), v_a_1245_, v_b_1246_, lean_box(0), v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
stack->m_obj
 = v_res_1255_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1___boxed(lean_object* v_upperBound_1256_, lean_object* v_inst_1257_, lean_object* v_R_1258_, lean_object* v_a_1259_, lean_object* v_b_1260_, lean_object* v_c_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__1(v_upperBound_1256_, v_inst_1257_, v_R_1258_, v_a_1259_, v_b_1260_, v_c_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v_upperBound_1256_);
return v_res_1268_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(lean_object* v_upperBound_1269_, lean_object* v_inst_1270_, lean_object* v_R_1271_, lean_object* v_a_1272_, lean_object* v_b_1273_, lean_object* v_c_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___redArg(v_upperBound_1269_, v_a_1272_, v_b_1273_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1269_ = stack[0].m_obj;
lean_object* v_a_1272_ = stack[3].m_obj;
lean_object* v_b_1273_ = stack[4].m_obj;
lean_object* v___y_1275_ = stack[6].m_obj;
lean_object* v___y_1276_ = stack[7].m_obj;
lean_object* v___y_1277_ = stack[8].m_obj;
lean_object* v___y_1278_ = stack[9].m_obj;
lean_object* v___y_1279_ = stack[10].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1269_, lean_box(0), lean_box(0), v_a_1272_, v_b_1273_, lean_box(0), v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
stack->m_obj
 = v_res_1282_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2___boxed(lean_object* v_upperBound_1283_, lean_object* v_inst_1284_, lean_object* v_R_1285_, lean_object* v_a_1286_, lean_object* v_b_1287_, lean_object* v_c_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_mkFieldParamsForComputedFields_spec__2(v_upperBound_1283_, v_inst_1284_, v_R_1285_, v_a_1286_, v_b_1287_, v_c_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec(v_upperBound_1283_);
return v_res_1295_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(size_t v_sz_1296_, size_t v_i_1297_, lean_object* v_bs_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_lt(v_i_1297_, v_sz_1296_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_bs_1298_);
return v___x_1305_;
}
else
{
lean_object* v_v_1306_; lean_object* v___x_1307_; lean_object* v_bs_x27_1308_; lean_object* v___x_1309_; 
v_v_1306_ = lean_array_uget(v_bs_1298_, v_i_1297_);
v___x_1307_ = lean_unsigned_to_nat(0u);
v_bs_x27_1308_ = lean_array_uset(v_bs_1298_, v_i_1297_, v___x_1307_);
v___x_1309_ = l_Lean_Compiler_LCNF_Param_toMono___redArg(v_v_1306_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1297_, v___x_1311_);
v___x_1313_ = lean_array_uset(v_bs_x27_1308_, v_i_1297_, v_a_1310_);
v_i_1297_ = v___x_1312_;
v_bs_1298_ = v___x_1313_;
goto _start;
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_bs_x27_1308_);
v_a_1315_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1309_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1309_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1296_ = stack[0].m_num;
size_t v_i_1297_ = stack[1].m_num;
lean_object* v_bs_1298_ = stack[2].m_obj;
lean_object* v___y_1299_ = stack[3].m_obj;
lean_object* v___y_1300_ = stack[4].m_obj;
lean_object* v___y_1301_ = stack[5].m_obj;
lean_object* v___y_1302_ = stack[6].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1296_, v_i_1297_, v_bs_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg___boxed(lean_object* v_sz_1324_, lean_object* v_i_1325_, lean_object* v_bs_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1324_);
lean_dec(v_sz_1324_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_boxed_1332_, v_i_boxed_1333_, v_bs_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
return v_res_1334_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1___redArg();
return v___x_1335_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(lean_object* v_msg_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_toApplicative_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1407_; 
v___x_1343_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1344_ = l_StateRefT_x27_instMonad___redArg(v___x_1343_);
v_toApplicative_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1344_, 1);
lean_dec(v_unused_1408_);
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1407_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_toApplicative_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1407_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_toFunctor_1349_; lean_object* v_toSeq_1350_; lean_object* v_toSeqLeft_1351_; lean_object* v_toSeqRight_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1405_; 
v_toFunctor_1349_ = lean_ctor_get(v_toApplicative_1345_, 0);
v_toSeq_1350_ = lean_ctor_get(v_toApplicative_1345_, 2);
v_toSeqLeft_1351_ = lean_ctor_get(v_toApplicative_1345_, 3);
v_toSeqRight_1352_ = lean_ctor_get(v_toApplicative_1345_, 4);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_toApplicative_1345_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_toApplicative_1345_, 1);
lean_dec(v_unused_1406_);
v___x_1354_ = v_toApplicative_1345_;
v_isShared_1355_ = v_isSharedCheck_1405_;
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
v_isShared_1355_ = v_isSharedCheck_1405_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___f_1359_; lean_object* v___x_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___x_1365_; 
v___f_1356_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1357_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
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
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v___f_1356_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v___f_1363_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v___f_1362_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v___f_1361_);
v___x_1365_ = v_reuseFailAlloc_1404_;
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
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___f_1357_);
v___x_1367_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v_toApplicative_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1401_; 
v___x_1368_ = l_StateRefT_x27_instMonad___redArg(v___x_1367_);
v_toApplicative_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1368_, 1);
lean_dec(v_unused_1402_);
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1401_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_toApplicative_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1401_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_toFunctor_1373_; lean_object* v_toSeq_1374_; lean_object* v_toSeqLeft_1375_; lean_object* v_toSeqRight_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1399_; 
v_toFunctor_1373_ = lean_ctor_get(v_toApplicative_1369_, 0);
v_toSeq_1374_ = lean_ctor_get(v_toApplicative_1369_, 2);
v_toSeqLeft_1375_ = lean_ctor_get(v_toApplicative_1369_, 3);
v_toSeqRight_1376_ = lean_ctor_get(v_toApplicative_1369_, 4);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_toApplicative_1369_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_toApplicative_1369_, 1);
lean_dec(v_unused_1400_);
v___x_1378_ = v_toApplicative_1369_;
v_isShared_1379_ = v_isSharedCheck_1399_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_toSeqRight_1376_);
lean_inc(v_toSeqLeft_1375_);
lean_inc(v_toSeq_1374_);
lean_inc(v_toFunctor_1373_);
lean_dec(v_toApplicative_1369_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1399_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___f_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___f_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___x_1389_; 
v___f_1380_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1381_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1373_);
v___f_1382_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1382_, 0, v_toFunctor_1373_);
v___f_1383_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1383_, 0, v_toFunctor_1373_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___f_1382_);
lean_ctor_set(v___x_1384_, 1, v___f_1383_);
v___f_1385_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1385_, 0, v_toSeqRight_1376_);
v___f_1386_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1386_, 0, v_toSeqLeft_1375_);
v___f_1387_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1387_, 0, v_toSeq_1374_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v___f_1385_);
lean_ctor_set(v___x_1378_, 3, v___f_1386_);
lean_ctor_set(v___x_1378_, 2, v___f_1387_);
lean_ctor_set(v___x_1378_, 1, v___f_1380_);
lean_ctor_set(v___x_1378_, 0, v___x_1384_);
v___x_1389_ = v___x_1378_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___f_1380_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v___f_1387_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v___f_1386_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v___f_1385_);
v___x_1389_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1391_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___f_1381_);
lean_ctor_set(v___x_1371_, 0, v___x_1389_);
v___x_1391_ = v___x_1371_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___f_1381_);
v___x_1391_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_30478__overap_1395_; lean_object* v___x_1396_; 
v___x_1392_ = l_StateRefT_x27_instMonad___redArg(v___x_1391_);
v___x_1393_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1394_ = l_instInhabitedOfMonad___redArg(v___x_1392_, v___x_1393_);
v___x_30478__overap_1395_ = lean_panic_fn_borrowed(v___x_1394_, v_msg_1336_);
lean_dec(v___x_1394_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
v___x_1396_ = lean_apply_6(v___x_30478__overap_1395_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, lean_box(0));
return v___x_1396_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1336_ = stack[0].m_obj;
lean_object* v___y_1337_ = stack[1].m_obj;
lean_object* v___y_1338_ = stack[2].m_obj;
lean_object* v___y_1339_ = stack[3].m_obj;
lean_object* v___y_1340_ = stack[4].m_obj;
lean_object* v___y_1341_ = stack[5].m_obj;
lean_object* v_res_1409_;
v_res_1409_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
stack->m_obj
 = v_res_1409_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___boxed(lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v_msg_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(lean_object* v_msg_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3___closed__0);
v___x_1420_ = lean_panic_fn_borrowed(v___x_1419_, v_msg_1418_);
return v___x_1420_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1___redArg();
return v___x_1421_;
}
}
lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_toApplicative_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1493_; 
v___x_1429_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0, &l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__0);
v___x_1430_ = l_StateRefT_x27_instMonad___redArg(v___x_1429_);
v_toApplicative_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1430_, 1);
lean_dec(v_unused_1494_);
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1493_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_toApplicative_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1493_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_toFunctor_1435_; lean_object* v_toSeq_1436_; lean_object* v_toSeqLeft_1437_; lean_object* v_toSeqRight_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1491_; 
v_toFunctor_1435_ = lean_ctor_get(v_toApplicative_1431_, 0);
v_toSeq_1436_ = lean_ctor_get(v_toApplicative_1431_, 2);
v_toSeqLeft_1437_ = lean_ctor_get(v_toApplicative_1431_, 3);
v_toSeqRight_1438_ = lean_ctor_get(v_toApplicative_1431_, 4);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_toApplicative_1431_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_toApplicative_1431_, 1);
lean_dec(v_unused_1492_);
v___x_1440_ = v_toApplicative_1431_;
v_isShared_1441_ = v_isSharedCheck_1491_;
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
v_isShared_1441_ = v_isSharedCheck_1491_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___f_1449_; lean_object* v___x_1451_; 
v___f_1442_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__1));
v___f_1443_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__2));
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
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___f_1442_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v___f_1449_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v___f_1448_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___f_1447_);
v___x_1451_ = v_reuseFailAlloc_1490_;
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
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___f_1443_);
v___x_1453_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v_toApplicative_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1487_; 
v___x_1454_ = l_StateRefT_x27_instMonad___redArg(v___x_1453_);
v_toApplicative_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1454_, 1);
lean_dec(v_unused_1488_);
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1487_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_toApplicative_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1487_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_toFunctor_1459_; lean_object* v_toSeq_1460_; lean_object* v_toSeqLeft_1461_; lean_object* v_toSeqRight_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1485_; 
v_toFunctor_1459_ = lean_ctor_get(v_toApplicative_1455_, 0);
v_toSeq_1460_ = lean_ctor_get(v_toApplicative_1455_, 2);
v_toSeqLeft_1461_ = lean_ctor_get(v_toApplicative_1455_, 3);
v_toSeqRight_1462_ = lean_ctor_get(v_toApplicative_1455_, 4);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_toApplicative_1455_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; 
v_unused_1486_ = lean_ctor_get(v_toApplicative_1455_, 1);
lean_dec(v_unused_1486_);
v___x_1464_ = v_toApplicative_1455_;
v_isShared_1465_ = v_isSharedCheck_1485_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_toSeqRight_1462_);
lean_inc(v_toSeqLeft_1461_);
lean_inc(v_toSeq_1460_);
lean_inc(v_toFunctor_1459_);
lean_dec(v_toApplicative_1455_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1485_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___f_1466_; lean_object* v___f_1467_; lean_object* v___f_1468_; lean_object* v___f_1469_; lean_object* v___x_1470_; lean_object* v___f_1471_; lean_object* v___f_1472_; lean_object* v___f_1473_; lean_object* v___x_1475_; 
v___f_1466_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__3));
v___f_1467_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_LetValue_toMono_spec__0___closed__4));
lean_inc_ref(v_toFunctor_1459_);
v___f_1468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1468_, 0, v_toFunctor_1459_);
v___f_1469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1469_, 0, v_toFunctor_1459_);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___f_1468_);
lean_ctor_set(v___x_1470_, 1, v___f_1469_);
v___f_1471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1471_, 0, v_toSeqRight_1462_);
v___f_1472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1472_, 0, v_toSeqLeft_1461_);
v___f_1473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1473_, 0, v_toSeq_1460_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___f_1471_);
lean_ctor_set(v___x_1464_, 3, v___f_1472_);
lean_ctor_set(v___x_1464_, 2, v___f_1473_);
lean_ctor_set(v___x_1464_, 1, v___f_1466_);
lean_ctor_set(v___x_1464_, 0, v___x_1470_);
v___x_1475_ = v___x_1464_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___f_1466_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v___f_1473_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v___f_1472_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v___f_1471_);
v___x_1475_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v___f_1467_);
lean_ctor_set(v___x_1457_, 0, v___x_1475_);
v___x_1477_ = v___x_1457_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___f_1467_);
v___x_1477_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_30493__overap_1481_; lean_object* v___x_1482_; 
v___x_1478_ = l_StateRefT_x27_instMonad___redArg(v___x_1477_);
v___x_1479_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1480_ = l_instInhabitedOfMonad___redArg(v___x_1478_, v___x_1479_);
v___x_30493__overap_1481_ = lean_panic_fn_borrowed(v___x_1480_, v_msg_1422_);
lean_dec(v___x_1480_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v___y_1425_);
lean_inc_ref(v___y_1424_);
lean_inc(v___y_1423_);
v___x_1482_ = lean_apply_6(v___x_30493__overap_1481_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, lean_box(0));
return v___x_1482_;
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
LEAN_EXPORT void l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1422_ = stack[0].m_obj;
lean_object* v___y_1423_ = stack[1].m_obj;
lean_object* v___y_1424_ = stack[2].m_obj;
lean_object* v___y_1425_ = stack[3].m_obj;
lean_object* v___y_1426_ = stack[4].m_obj;
lean_object* v___y_1427_ = stack[5].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
stack->m_obj
 = v_res_1495_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___boxed(lean_object* v_msg_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v_msg_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
return v_res_1503_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1506_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1507_ = lean_unsigned_to_nat(9u);
v___x_1508_ = lean_unsigned_to_nat(650u);
v___x_1509_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__1));
v___x_1510_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__0));
v___x_1511_ = l_mkPanicMessageWithDecl(v___x_1510_, v___x_1509_, v___x_1508_, v___x_1507_, v___x_1506_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1514_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__3));
v___x_1515_ = lean_unsigned_to_nat(66u);
v___x_1516_ = lean_unsigned_to_nat(363u);
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1518_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1519_ = l_mkPanicMessageWithDecl(v___x_1518_, v___x_1517_, v___x_1516_, v___x_1515_, v___x_1514_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1520_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1521_ = lean_unsigned_to_nat(27u);
v___x_1522_ = lean_unsigned_to_nat(319u);
v___x_1523_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1524_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1525_ = l_mkPanicMessageWithDecl(v___x_1524_, v___x_1523_, v___x_1522_, v___x_1521_, v___x_1520_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1580_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1581_ = lean_unsigned_to_nat(2u);
v___x_1582_ = lean_unsigned_to_nat(302u);
v___x_1583_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1584_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1585_ = l_mkPanicMessageWithDecl(v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__2));
v___x_1588_ = lean_unsigned_to_nat(2u);
v___x_1589_ = lean_unsigned_to_nat(304u);
v___x_1590_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1591_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1592_ = l_mkPanicMessageWithDecl(v___x_1591_, v___x_1590_, v___x_1589_, v___x_1588_, v___x_1587_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1594_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__4));
v___x_1595_ = lean_unsigned_to_nat(2u);
v___x_1596_ = lean_unsigned_to_nat(305u);
v___x_1597_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1598_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1599_ = l_mkPanicMessageWithDecl(v___x_1598_, v___x_1597_, v___x_1596_, v___x_1595_, v___x_1594_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3(void){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Lean_Compiler_LCNF_instInhabitedParam_default___redArg();
return v___x_1600_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1601_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1602_ = lean_unsigned_to_nat(41u);
v___x_1603_ = lean_unsigned_to_nat(303u);
v___x_1604_ = ((lean_object*)(l_Lean_Compiler_LCNF_trivialStructToMono___closed__0));
v___x_1605_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1606_ = l_mkPanicMessageWithDecl(v___x_1605_, v___x_1604_, v___x_1603_, v___x_1602_, v___x_1601_);
return v___x_1606_;
}
}
lean_object* l_Lean_Compiler_LCNF_trivialStructToMono(lean_object* v_info_1607_, lean_object* v_c_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_discr_1615_; lean_object* v_alts_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1694_; 
v_discr_1615_ = lean_ctor_get(v_c_1608_, 2);
v_alts_1616_ = lean_ctor_get(v_c_1608_, 3);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_c_1608_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; lean_object* v_unused_1696_; 
v_unused_1695_ = lean_ctor_get(v_c_1608_, 1);
lean_dec(v_unused_1695_);
v_unused_1696_ = lean_ctor_get(v_c_1608_, 0);
lean_dec(v_unused_1696_);
v___x_1618_ = v_c_1608_;
v_isShared_1619_ = v_isSharedCheck_1694_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_alts_1616_);
lean_inc(v_discr_1615_);
lean_dec(v_c_1608_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1694_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1620_ = lean_array_get_size(v_alts_1616_);
v___x_1621_ = lean_unsigned_to_nat(1u);
v___x_1622_ = lean_nat_dec_eq(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
lean_del_object(v___x_1618_);
lean_dec_ref(v_alts_1616_);
lean_dec(v_discr_1615_);
v___x_1623_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__1, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__1_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__1);
v___x_1624_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1623_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1624_;
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = lean_array_get(v___x_1625_, v_alts_1616_, v___x_1626_);
lean_dec_ref(v_alts_1616_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_ctorName_1628_; lean_object* v_params_1629_; lean_object* v_code_1630_; lean_object* v_ctorName_1631_; lean_object* v_fieldIdx_1632_; uint8_t v___x_1633_; 
v_ctorName_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_ctorName_1628_);
v_params_1629_ = lean_ctor_get(v___x_1627_, 1);
lean_inc_ref(v_params_1629_);
v_code_1630_ = lean_ctor_get(v___x_1627_, 2);
lean_inc_ref(v_code_1630_);
lean_dec_ref_known(v___x_1627_, 3);
v_ctorName_1631_ = lean_ctor_get(v_info_1607_, 0);
v_fieldIdx_1632_ = lean_ctor_get(v_info_1607_, 2);
v___x_1633_ = lean_name_eq(v_ctorName_1628_, v_ctorName_1631_);
lean_dec(v_ctorName_1628_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_code_1630_);
lean_dec_ref(v_params_1629_);
lean_del_object(v___x_1618_);
lean_dec(v_discr_1615_);
v___x_1634_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__3, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__3_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__3);
v___x_1635_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1634_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = lean_array_get_size(v_params_1629_);
v___x_1637_ = lean_nat_dec_lt(v_fieldIdx_1632_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_code_1630_);
lean_dec_ref(v_params_1629_);
lean_del_object(v___x_1618_);
lean_dec(v_discr_1615_);
v___x_1638_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__5, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__5_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__5);
v___x_1639_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1638_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1639_;
}
else
{
uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v_p_1642_; lean_object* v___x_1643_; 
v___x_1640_ = 0;
v___x_1641_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v_p_1642_ = lean_array_get(v___x_1641_, v_params_1629_, v_fieldIdx_1632_);
v___x_1643_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1640_, v_params_1629_, v_a_1611_);
lean_dec_ref(v_params_1629_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_fvarId_1644_; lean_object* v_binderName_1645_; lean_object* v_type_1646_; lean_object* v___x_1647_; 
lean_dec_ref_known(v___x_1643_, 1);
v_fvarId_1644_ = lean_ctor_get(v_p_1642_, 0);
lean_inc(v_fvarId_1644_);
v_binderName_1645_ = lean_ctor_get(v_p_1642_, 1);
lean_inc(v_binderName_1645_);
v_type_1646_ = lean_ctor_get(v_p_1642_, 2);
lean_inc_ref(v_type_1646_);
lean_dec(v_p_1642_);
v___x_1647_ = l_Lean_Compiler_LCNF_toMonoType(v_type_1646_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = ((lean_object*)(l_Lean_Compiler_LCNF_ctorAppToMono___closed__0));
v___x_1650_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_discr_1615_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 3, v___x_1650_);
lean_ctor_set(v___x_1618_, 2, v_a_1648_);
lean_ctor_set(v___x_1618_, 1, v_binderName_1645_);
lean_ctor_set(v___x_1618_, 0, v_fvarId_1644_);
v___x_1652_ = v___x_1618_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_fvarId_1644_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_binderName_1645_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_a_1648_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v_lctx_1654_; lean_object* v_nextIdx_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1674_; 
v___x_1653_ = lean_st_ref_take(v_a_1611_);
v_lctx_1654_ = lean_ctor_get(v___x_1653_, 0);
v_nextIdx_1655_ = lean_ctor_get(v___x_1653_, 1);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1657_ = v___x_1653_;
v_isShared_1658_ = v_isSharedCheck_1674_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_nextIdx_1655_);
lean_inc(v_lctx_1654_);
lean_dec(v___x_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1674_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_inc_ref(v___x_1652_);
v___x_1659_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1640_, v_lctx_1654_, v___x_1652_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_nextIdx_1655_);
v___x_1661_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_st_ref_put(v_a_1611_, v___x_1661_);
v___x_1663_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1630_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1672_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1663_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1666_ = v___x_1663_;
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1663_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1672_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1652_);
lean_ctor_set(v___x_1668_, 1, v_a_1664_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_dec_ref(v___x_1652_);
return v___x_1663_;
}
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v_binderName_1645_);
lean_dec(v_fvarId_1644_);
lean_dec_ref(v_code_1630_);
lean_del_object(v___x_1618_);
lean_dec(v_discr_1615_);
v_a_1676_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1647_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1647_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_dec(v_p_1642_);
lean_dec_ref(v_code_1630_);
lean_del_object(v___x_1618_);
lean_dec(v_discr_1615_);
v_a_1684_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1643_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1643_);
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
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v___x_1627_);
lean_del_object(v___x_1618_);
lean_dec(v_discr_1615_);
v___x_1692_ = lean_obj_once(&l_Lean_Compiler_LCNF_trivialStructToMono___closed__6, &l_Lean_Compiler_LCNF_trivialStructToMono___closed__6_once, _init_l_Lean_Compiler_LCNF_trivialStructToMono___closed__6);
v___x_1693_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1692_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
return v___x_1693_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_trivialStructToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1607_ = stack[0].m_obj;
lean_object* v_c_1608_ = stack[1].m_obj;
lean_object* v_a_1609_ = stack[2].m_obj;
lean_object* v_a_1610_ = stack[3].m_obj;
lean_object* v_a_1611_ = stack[4].m_obj;
lean_object* v_a_1612_ = stack[5].m_obj;
lean_object* v_a_1613_ = stack[6].m_obj;
lean_object* v_res_1697_;
v_res_1697_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_1607_, v_c_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
stack->m_obj
 = v_res_1697_;
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__1));
v___x_1703_ = lean_unsigned_to_nat(70u);
v___x_1704_ = lean_unsigned_to_nat(373u);
v___x_1705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__0));
v___x_1706_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1707_ = l_mkPanicMessageWithDecl(v___x_1706_, v___x_1705_, v___x_1704_, v___x_1703_, v___x_1702_);
return v___x_1707_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(lean_object* v___x_1708_, uint8_t v___x_1709_, size_t v_sz_1710_, size_t v_i_1711_, lean_object* v_bs_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_usize_dec_lt(v_i_1711_, v_sz_1710_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref(v___x_1708_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_bs_1712_);
return v___x_1720_;
}
else
{
lean_object* v_v_1721_; lean_object* v___x_1722_; lean_object* v_bs_x27_1723_; lean_object* v_a_1725_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; 
v_v_1721_ = lean_array_uget(v_bs_1712_, v_i_1711_);
v___x_1722_ = lean_unsigned_to_nat(0u);
v_bs_x27_1723_ = lean_array_uset(v_bs_1712_, v_i_1711_, v___x_1722_);
if (lean_obj_tag(v_v_1721_) == 0)
{
lean_object* v_ctorName_1747_; lean_object* v_params_1748_; lean_object* v_code_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1787_; 
v_ctorName_1747_ = lean_ctor_get(v_v_1721_, 0);
v_params_1748_ = lean_ctor_get(v_v_1721_, 1);
v_code_1749_ = lean_ctor_get(v_v_1721_, 2);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_v_1721_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1751_ = v_v_1721_;
v_isShared_1752_ = v_isSharedCheck_1787_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_code_1749_);
lean_inc(v_params_1748_);
lean_inc(v_ctorName_1747_);
lean_dec(v_v_1721_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1787_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_1754_ = l_Lean_Name_append(v_ctorName_1747_, v___x_1753_);
lean_inc(v___x_1754_);
lean_inc_ref(v___x_1708_);
v___x_1755_ = l_Lean_Environment_find_x3f(v___x_1708_, v___x_1754_, v___x_1709_);
if (lean_obj_tag(v___x_1755_) == 1)
{
lean_object* v_val_1756_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v___x_1755_, 1);
if (lean_obj_tag(v_val_1756_) == 6)
{
lean_object* v_val_1757_; lean_object* v_toConstantVal_1758_; lean_object* v_numParams_1759_; lean_object* v_numFields_1760_; lean_object* v_type_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v_val_1757_ = lean_ctor_get(v_val_1756_, 0);
lean_inc_ref(v_val_1757_);
lean_dec_ref_known(v_val_1756_, 1);
v_toConstantVal_1758_ = lean_ctor_get(v_val_1757_, 0);
lean_inc_ref(v_toConstantVal_1758_);
v_numParams_1759_ = lean_ctor_get(v_val_1757_, 3);
lean_inc(v_numParams_1759_);
v_numFields_1760_ = lean_ctor_get(v_val_1757_, 4);
lean_inc(v_numFields_1760_);
lean_dec_ref(v_val_1757_);
v_type_1761_ = lean_ctor_get(v_toConstantVal_1758_, 2);
lean_inc_ref(v_type_1761_);
lean_dec_ref(v_toConstantVal_1758_);
v___x_1762_ = lean_array_get_size(v_params_1748_);
v___x_1763_ = lean_nat_sub(v_numFields_1760_, v___x_1762_);
lean_dec(v_numFields_1760_);
v___x_1764_ = l_Lean_Compiler_LCNF_mkFieldParamsForComputedFields(v_type_1761_, v_numParams_1759_, v___x_1763_, v_params_1748_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
lean_dec_ref(v_params_1748_);
lean_dec(v___x_1763_);
lean_dec(v_numParams_1759_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1749_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 2, v_a_1767_);
lean_ctor_set(v___x_1751_, 1, v_a_1765_);
lean_ctor_set(v___x_1751_, 0, v___x_1754_);
v___x_1769_ = v___x_1751_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_a_1765_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_a_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
v_a_1725_ = v___x_1769_;
goto v___jp_1724_;
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1765_);
lean_dec(v___x_1754_);
lean_del_object(v___x_1751_);
lean_dec_ref(v_bs_x27_1723_);
lean_dec_ref(v___x_1708_);
v_a_1771_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1766_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1766_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v___x_1754_);
lean_del_object(v___x_1751_);
lean_dec_ref(v_code_1749_);
lean_dec_ref(v_bs_x27_1723_);
lean_dec_ref(v___x_1708_);
v_a_1779_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1764_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1764_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
else
{
lean_dec(v_val_1756_);
lean_dec(v___x_1754_);
lean_del_object(v___x_1751_);
lean_dec_ref(v_code_1749_);
lean_dec_ref(v_params_1748_);
v___y_1731_ = v___y_1713_;
v___y_1732_ = v___y_1714_;
v___y_1733_ = v___y_1715_;
v___y_1734_ = v___y_1716_;
v___y_1735_ = v___y_1717_;
goto v___jp_1730_;
}
}
else
{
lean_dec(v___x_1755_);
lean_dec(v___x_1754_);
lean_del_object(v___x_1751_);
lean_dec_ref(v_code_1749_);
lean_dec_ref(v_params_1748_);
v___y_1731_ = v___y_1713_;
v___y_1732_ = v___y_1714_;
v___y_1733_ = v___y_1715_;
v___y_1734_ = v___y_1716_;
v___y_1735_ = v___y_1717_;
goto v___jp_1730_;
}
}
}
else
{
lean_object* v_code_1788_; lean_object* v___x_1789_; 
v_code_1788_ = lean_ctor_get(v_v_1721_, 0);
lean_inc_ref(v_code_1788_);
v___x_1789_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1788_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1791_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v___x_1791_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1721_, v_a_1790_);
v_a_1725_ = v___x_1791_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref_known(v_v_1721_, 1);
lean_dec_ref(v_bs_x27_1723_);
lean_dec_ref(v___x_1708_);
v_a_1792_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1789_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1789_);
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
v___jp_1724_:
{
size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1711_, v___x_1726_);
v___x_1728_ = lean_array_uset(v_bs_x27_1723_, v_i_1711_, v_a_1725_);
v_i_1711_ = v___x_1727_;
v_bs_1712_ = v___x_1728_;
goto _start;
}
v___jp_1730_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__2);
v___x_1737_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4(v___x_1736_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v_a_1725_ = v_a_1738_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v_bs_x27_1723_);
lean_dec_ref(v___x_1708_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
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
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1708_ = stack[0].m_obj;
uint8_t v___x_1709_ = stack[1].m_num;
size_t v_sz_1710_ = stack[2].m_num;
size_t v_i_1711_ = stack[3].m_num;
lean_object* v_bs_1712_ = stack[4].m_obj;
lean_object* v___y_1713_ = stack[5].m_obj;
lean_object* v___y_1714_ = stack[6].m_obj;
lean_object* v___y_1715_ = stack[7].m_obj;
lean_object* v___y_1716_ = stack[8].m_obj;
lean_object* v___y_1717_ = stack[9].m_obj;
lean_object* v_res_1800_;
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_1708_, v___x_1709_, v_sz_1710_, v_i_1711_, v_bs_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
stack->m_obj
 = v_res_1800_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(size_t v_sz_1801_, size_t v_i_1802_, lean_object* v_bs_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = lean_usize_dec_lt(v_i_1802_, v_sz_1801_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; 
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_bs_1803_);
return v___x_1811_;
}
else
{
lean_object* v_v_1812_; lean_object* v___x_1813_; lean_object* v_bs_x27_1814_; lean_object* v_a_1816_; 
v_v_1812_ = lean_array_uget(v_bs_1803_, v_i_1802_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v_bs_x27_1814_ = lean_array_uset(v_bs_1803_, v_i_1802_, v___x_1813_);
if (lean_obj_tag(v_v_1812_) == 0)
{
lean_object* v_params_1821_; lean_object* v_code_1822_; uint8_t v___x_1823_; size_t v_sz_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v_params_1821_ = lean_ctor_get(v_v_1812_, 1);
v_code_1822_ = lean_ctor_get(v_v_1812_, 2);
v___x_1823_ = 0;
v_sz_1824_ = lean_array_size(v_params_1821_);
v___x_1825_ = ((size_t)0ULL);
lean_inc_ref(v_params_1821_);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_1824_, v___x_1825_, v_params_1821_, v___y_1804_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
lean_inc_ref(v_code_1822_);
v___x_1828_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1822_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 1);
v___x_1830_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltImp(v___x_1823_, v_v_1812_, v_a_1827_, v_a_1829_);
v_a_1816_ = v___x_1830_;
goto v___jp_1815_;
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1827_);
lean_dec_ref_known(v_v_1812_, 3);
lean_dec_ref(v_bs_x27_1814_);
v_a_1831_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1828_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1828_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
else
{
lean_dec_ref_known(v_v_1812_, 3);
lean_dec_ref(v_bs_x27_1814_);
return v___x_1826_;
}
}
else
{
lean_object* v_code_1839_; lean_object* v___x_1840_; 
v_code_1839_ = lean_ctor_get(v_v_1812_, 0);
lean_inc_ref(v_code_1839_);
v___x_1840_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1839_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_1812_, v_a_1841_);
v_a_1816_ = v___x_1842_;
goto v___jp_1815_;
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec_ref_known(v_v_1812_, 1);
lean_dec_ref(v_bs_x27_1814_);
v_a_1843_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1840_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1840_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
v___jp_1815_:
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_add(v_i_1802_, v___x_1817_);
v___x_1819_ = lean_array_uset(v_bs_x27_1814_, v_i_1802_, v_a_1816_);
v_i_1802_ = v___x_1818_;
v_bs_1803_ = v___x_1819_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1801_ = stack[0].m_num;
size_t v_i_1802_ = stack[1].m_num;
lean_object* v_bs_1803_ = stack[2].m_obj;
lean_object* v___y_1804_ = stack[3].m_obj;
lean_object* v___y_1805_ = stack[4].m_obj;
lean_object* v___y_1806_ = stack[5].m_obj;
lean_object* v___y_1807_ = stack[6].m_obj;
lean_object* v___y_1808_ = stack[7].m_obj;
lean_object* v_res_1851_;
v_res_1851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_1801_, v_i_1802_, v_bs_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
stack->m_obj
 = v_res_1851_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1853_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1854_ = lean_unsigned_to_nat(2u);
v___x_1855_ = lean_unsigned_to_nat(291u);
v___x_1856_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1857_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1858_ = l_mkPanicMessageWithDecl(v___x_1857_, v___x_1856_, v___x_1855_, v___x_1854_, v___x_1853_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = lean_unsigned_to_nat(2u);
v___x_1865_ = lean_mk_empty_array_with_capacity(v___x_1864_);
v___x_1866_ = lean_array_push(v___x_1865_, v___x_1863_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1867_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1868_ = lean_unsigned_to_nat(34u);
v___x_1869_ = lean_unsigned_to_nat(292u);
v___x_1870_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__0));
v___x_1871_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1872_ = l_mkPanicMessageWithDecl(v___x_1871_, v___x_1870_, v___x_1869_, v___x_1868_, v___x_1867_);
return v___x_1872_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg(lean_object* v_c_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_discr_1880_; lean_object* v_alts_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1950_; 
v_discr_1880_ = lean_ctor_get(v_c_1873_, 2);
v_alts_1881_ = lean_ctor_get(v_c_1873_, 3);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_c_1873_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; lean_object* v_unused_1952_; 
v_unused_1951_ = lean_ctor_get(v_c_1873_, 1);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_c_1873_, 0);
lean_dec(v_unused_1952_);
v___x_1883_ = v_c_1873_;
v_isShared_1884_ = v_isSharedCheck_1950_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_alts_1881_);
lean_inc(v_discr_1880_);
lean_dec(v_c_1873_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1950_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1885_ = lean_array_get_size(v_alts_1881_);
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = lean_nat_dec_eq(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_del_object(v___x_1883_);
lean_dec_ref(v_alts_1881_);
lean_dec(v_discr_1880_);
v___x_1888_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__1);
v___x_1889_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1888_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_array_get(v___x_1890_, v_alts_1881_, v___x_1891_);
lean_dec_ref(v_alts_1881_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_params_1893_; lean_object* v_code_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1946_; 
v_params_1893_ = lean_ctor_get(v___x_1892_, 1);
v_code_1894_ = lean_ctor_get(v___x_1892_, 2);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1947_);
v___x_1896_ = v___x_1892_;
v_isShared_1897_ = v_isSharedCheck_1946_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_code_1894_);
lean_inc(v_params_1893_);
lean_dec(v___x_1892_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1946_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
uint8_t v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = 0;
v___x_1899_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_1900_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1898_, v_params_1893_, v_a_1876_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v___x_1901_; lean_object* v_fvarId_1902_; lean_object* v_binderName_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec_ref_known(v___x_1900_, 1);
v___x_1901_ = lean_array_get(v___x_1899_, v_params_1893_, v___x_1891_);
lean_dec_ref(v_params_1893_);
v_fvarId_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_fvarId_1902_);
v_binderName_1903_ = lean_ctor_get(v___x_1901_, 1);
lean_inc(v_binderName_1903_);
lean_dec(v___x_1901_);
v___x_1904_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_1905_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__4));
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v_discr_1880_);
v___x_1908_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_1909_ = lean_array_push(v___x_1908_, v___x_1907_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 3);
lean_ctor_set(v___x_1896_, 2, v___x_1909_);
lean_ctor_set(v___x_1896_, 1, v___x_1906_);
lean_ctor_set(v___x_1896_, 0, v___x_1905_);
v___x_1911_ = v___x_1896_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 3, v___x_1911_);
lean_ctor_set(v___x_1883_, 2, v___x_1904_);
lean_ctor_set(v___x_1883_, 1, v_binderName_1903_);
lean_ctor_set(v___x_1883_, 0, v_fvarId_1902_);
v___x_1913_ = v___x_1883_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fvarId_1902_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_binderName_1903_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v_lctx_1915_; lean_object* v_nextIdx_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1935_; 
v___x_1914_ = lean_st_ref_take(v_a_1876_);
v_lctx_1915_ = lean_ctor_get(v___x_1914_, 0);
v_nextIdx_1916_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1918_ = v___x_1914_;
v_isShared_1919_ = v_isSharedCheck_1935_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_nextIdx_1916_);
lean_inc(v_lctx_1915_);
lean_dec(v___x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1935_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
lean_inc_ref(v___x_1913_);
v___x_1920_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1898_, v_lctx_1915_, v___x_1913_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_nextIdx_1916_);
v___x_1922_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_st_ref_put(v_a_1876_, v___x_1922_);
v___x_1924_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1894_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1933_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1933_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1913_);
lean_ctor_set(v___x_1929_, 1, v_a_1925_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
else
{
lean_dec_ref(v___x_1913_);
return v___x_1924_;
}
}
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_del_object(v___x_1896_);
lean_dec_ref(v_code_1894_);
lean_dec_ref(v_params_1893_);
lean_del_object(v___x_1883_);
lean_dec(v_discr_1880_);
v_a_1938_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1900_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1900_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v___x_1892_);
lean_del_object(v___x_1883_);
lean_dec(v_discr_1880_);
v___x_1948_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesTaskToMono___redArg___closed__5);
v___x_1949_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1948_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesTaskToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1873_ = stack[0].m_obj;
lean_object* v_a_1874_ = stack[1].m_obj;
lean_object* v_a_1875_ = stack[2].m_obj;
lean_object* v_a_1876_ = stack[3].m_obj;
lean_object* v_a_1877_ = stack[4].m_obj;
lean_object* v_a_1878_ = stack[5].m_obj;
lean_object* v_res_1953_;
v_res_1953_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
stack->m_obj
 = v_res_1953_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1955_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_1956_ = lean_unsigned_to_nat(2u);
v___x_1957_ = lean_unsigned_to_nat(271u);
v___x_1958_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1959_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1960_ = l_mkPanicMessageWithDecl(v___x_1959_, v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_box(0);
v___x_1968_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__7));
v___x_1969_ = l_Lean_Expr_const___override(v___x_1968_, v___x_1967_);
return v___x_1969_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1970_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_1971_ = lean_unsigned_to_nat(34u);
v___x_1972_ = lean_unsigned_to_nat(272u);
v___x_1973_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__0));
v___x_1974_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_1975_ = l_mkPanicMessageWithDecl(v___x_1974_, v___x_1973_, v___x_1972_, v___x_1971_, v___x_1970_);
return v___x_1975_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg(lean_object* v_c_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_discr_1983_; lean_object* v_alts_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_discr_1983_ = lean_ctor_get(v_c_1976_, 2);
v_alts_1984_ = lean_ctor_get(v_c_1976_, 3);
v___x_1985_ = lean_array_get_size(v_alts_1984_);
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_dec_eq(v___x_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__1);
v___x_1989_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_1988_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
return v___x_1989_;
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_array_get(v___x_1990_, v_alts_1984_, v___x_1991_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_params_1993_; lean_object* v_code_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2092_; 
v_params_1993_ = lean_ctor_get(v___x_1992_, 1);
v_code_1994_ = lean_ctor_get(v___x_1992_, 2);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v___x_1992_, 0);
lean_dec(v_unused_2093_);
v___x_1996_ = v___x_1992_;
v_isShared_1997_ = v_isSharedCheck_2092_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_code_1994_);
lean_inc(v_params_1993_);
lean_dec(v___x_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2092_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = 0;
v___x_1999_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2000_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_1998_, v_params_1993_, v_a_1979_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2008_; 
lean_dec_ref_known(v___x_2000_, 1);
v___x_2001_ = lean_array_get(v___x_1999_, v_params_1993_, v___x_1991_);
lean_dec_ref(v_params_1993_);
v___x_2002_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__3));
v___x_2003_ = lean_box(0);
lean_inc(v_discr_1983_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_discr_1983_);
v___x_2005_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2006_ = lean_array_push(v___x_2005_, v___x_2004_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 3);
lean_ctor_set(v___x_1996_, 2, v___x_2006_);
lean_ctor_set(v___x_1996_, 1, v___x_2003_);
lean_ctor_set(v___x_1996_, 0, v___x_2002_);
v___x_2008_ = v___x_1996_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_2010_ = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(v___x_2009_, v_a_1979_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2013_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1998_, v_a_2011_, v___x_2012_, v___x_2008_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; lean_object* v___x_2017_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__8);
v___x_2016_ = 0;
v___x_2017_ = l_Lean_Compiler_LCNF_mkAuxParam(v___x_1998_, v___x_2015_, v___x_2016_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = l_Lean_mkArrow(v___x_2015_, v___x_2012_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v_fvarId_2021_; lean_object* v_binderName_2022_; lean_object* v_fvarId_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v_lctx_2030_; lean_object* v_nextIdx_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2050_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v_fvarId_2021_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_fvarId_2021_);
v_binderName_2022_ = lean_ctor_get(v___x_2001_, 1);
lean_inc(v_binderName_2022_);
lean_dec(v___x_2001_);
v_fvarId_2023_ = lean_ctor_get(v_a_2014_, 0);
v___x_2024_ = lean_mk_empty_array_with_capacity(v___x_1986_);
v___x_2025_ = lean_array_push(v___x_2024_, v_a_2018_);
lean_inc(v_fvarId_2023_);
v___x_2026_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2026_, 0, v_fvarId_2023_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_a_2014_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2028_, 0, v_fvarId_2021_);
lean_ctor_set(v___x_2028_, 1, v_binderName_2022_);
lean_ctor_set(v___x_2028_, 2, v___x_2025_);
lean_ctor_set(v___x_2028_, 3, v_a_2020_);
lean_ctor_set(v___x_2028_, 4, v___x_2027_);
v___x_2029_ = lean_st_ref_take(v_a_1979_);
v_lctx_2030_ = lean_ctor_get(v___x_2029_, 0);
v_nextIdx_2031_ = lean_ctor_get(v___x_2029_, 1);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2033_ = v___x_2029_;
v_isShared_2034_ = v_isSharedCheck_2050_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_nextIdx_2031_);
lean_inc(v_lctx_2030_);
lean_dec(v___x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2050_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_inc_ref(v___x_2028_);
v___x_2035_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_1998_, v_lctx_2030_, v___x_2028_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_nextIdx_2031_);
v___x_2037_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_st_ref_put(v_a_1979_, v___x_2037_);
v___x_2039_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_1994_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2048_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2028_);
lean_ctor_set(v___x_2044_, 1, v_a_2040_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2044_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
lean_dec_ref_known(v___x_2028_, 5);
return v___x_2039_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_a_2018_);
lean_dec(v_a_2014_);
lean_dec(v___x_2001_);
lean_dec_ref(v_code_1994_);
v_a_2051_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2019_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2019_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2014_);
lean_dec(v___x_2001_);
lean_dec_ref(v_code_1994_);
v_a_2059_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2017_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2017_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v___x_2001_);
lean_dec_ref(v_code_1994_);
v_a_2067_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2013_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2013_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec_ref(v___x_2008_);
lean_dec(v___x_2001_);
lean_dec_ref(v_code_1994_);
v_a_2075_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2010_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2010_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_del_object(v___x_1996_);
lean_dec_ref(v_code_1994_);
lean_dec_ref(v_params_1993_);
v_a_2084_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2000_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2000_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v___x_1992_);
v___x_2094_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9, &l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9_once, _init_l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__9);
v___x_2095_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2094_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
return v___x_2095_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesThunkToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1976_ = stack[0].m_obj;
lean_object* v_a_1977_ = stack[1].m_obj;
lean_object* v_a_1978_ = stack[2].m_obj;
lean_object* v_a_1979_ = stack[3].m_obj;
lean_object* v_a_1980_ = stack[4].m_obj;
lean_object* v_a_1981_ = stack[5].m_obj;
lean_object* v_res_2096_;
v_res_2096_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
stack->m_obj
 = v_res_2096_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2098_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2099_ = lean_unsigned_to_nat(2u);
v___x_2100_ = lean_unsigned_to_nat(260u);
v___x_2101_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2102_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2103_ = l_mkPanicMessageWithDecl(v___x_2102_, v___x_2101_, v___x_2100_, v___x_2099_, v___x_2098_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2108_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2109_ = lean_unsigned_to_nat(34u);
v___x_2110_ = lean_unsigned_to_nat(261u);
v___x_2111_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__0));
v___x_2112_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2113_ = l_mkPanicMessageWithDecl(v___x_2112_, v___x_2111_, v___x_2110_, v___x_2109_, v___x_2108_);
return v___x_2113_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(lean_object* v_c_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_discr_2121_; lean_object* v_alts_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2191_; 
v_discr_2121_ = lean_ctor_get(v_c_2114_, 2);
v_alts_2122_ = lean_ctor_get(v_c_2114_, 3);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_c_2114_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; lean_object* v_unused_2193_; 
v_unused_2192_ = lean_ctor_get(v_c_2114_, 1);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_c_2114_, 0);
lean_dec(v_unused_2193_);
v___x_2124_ = v_c_2114_;
v_isShared_2125_ = v_isSharedCheck_2191_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_alts_2122_);
lean_inc(v_discr_2121_);
lean_dec(v_c_2114_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2191_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2126_ = lean_array_get_size(v_alts_2122_);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_nat_dec_eq(v___x_2126_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_del_object(v___x_2124_);
lean_dec_ref(v_alts_2122_);
lean_dec(v_discr_2121_);
v___x_2129_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__1);
v___x_2130_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2129_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_array_get(v___x_2131_, v_alts_2122_, v___x_2132_);
lean_dec_ref(v_alts_2122_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_params_2134_; lean_object* v_code_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2187_; 
v_params_2134_ = lean_ctor_get(v___x_2133_, 1);
v_code_2135_ = lean_ctor_get(v___x_2133_, 2);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; 
v_unused_2188_ = lean_ctor_get(v___x_2133_, 0);
lean_dec(v_unused_2188_);
v___x_2137_ = v___x_2133_;
v_isShared_2138_ = v_isSharedCheck_2187_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_code_2135_);
lean_inc(v_params_2134_);
lean_dec(v___x_2133_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2187_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = 0;
v___x_2140_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2141_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2139_, v_params_2134_, v_a_2117_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; lean_object* v_fvarId_2143_; lean_object* v_binderName_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_dec_ref_known(v___x_2141_, 1);
v___x_2142_ = lean_array_get(v___x_2140_, v_params_2134_, v___x_2132_);
lean_dec_ref(v_params_2134_);
v_fvarId_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_fvarId_2143_);
v_binderName_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_binderName_2144_);
lean_dec(v___x_2142_);
v___x_2145_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2146_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__4));
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v_discr_2121_);
v___x_2149_ = lean_mk_empty_array_with_capacity(v___x_2127_);
v___x_2150_ = lean_array_push(v___x_2149_, v___x_2148_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 3);
lean_ctor_set(v___x_2137_, 2, v___x_2150_);
lean_ctor_set(v___x_2137_, 1, v___x_2147_);
lean_ctor_set(v___x_2137_, 0, v___x_2146_);
v___x_2152_ = v___x_2137_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 3, v___x_2152_);
lean_ctor_set(v___x_2124_, 2, v___x_2145_);
lean_ctor_set(v___x_2124_, 1, v_binderName_2144_);
lean_ctor_set(v___x_2124_, 0, v_fvarId_2143_);
v___x_2154_ = v___x_2124_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_fvarId_2143_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_binderName_2144_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v_lctx_2156_; lean_object* v_nextIdx_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2176_; 
v___x_2155_ = lean_st_ref_take(v_a_2117_);
v_lctx_2156_ = lean_ctor_get(v___x_2155_, 0);
v_nextIdx_2157_ = lean_ctor_get(v___x_2155_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2159_ = v___x_2155_;
v_isShared_2160_ = v_isSharedCheck_2176_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_nextIdx_2157_);
lean_inc(v_lctx_2156_);
lean_dec(v___x_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2176_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_inc_ref(v___x_2154_);
v___x_2161_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2139_, v_lctx_2156_, v___x_2154_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_nextIdx_2157_);
v___x_2163_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_st_ref_put(v_a_2117_, v___x_2163_);
v___x_2165_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2135_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2174_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2174_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2154_);
lean_ctor_set(v___x_2170_, 1, v_a_2166_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 0, v___x_2170_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
lean_dec_ref(v___x_2154_);
return v___x_2165_;
}
}
}
}
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_del_object(v___x_2137_);
lean_dec_ref(v_code_2135_);
lean_dec_ref(v_params_2134_);
lean_del_object(v___x_2124_);
lean_dec(v_discr_2121_);
v_a_2179_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2141_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2141_);
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
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v___x_2133_);
lean_del_object(v___x_2124_);
lean_dec(v_discr_2121_);
v___x_2189_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___closed__5);
v___x_2190_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2189_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2190_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2114_ = stack[0].m_obj;
lean_object* v_a_2115_ = stack[1].m_obj;
lean_object* v_a_2116_ = stack[2].m_obj;
lean_object* v_a_2117_ = stack[3].m_obj;
lean_object* v_a_2118_ = stack[4].m_obj;
lean_object* v_a_2119_ = stack[5].m_obj;
lean_object* v_res_2194_;
v_res_2194_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
stack->m_obj
 = v_res_2194_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2196_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2197_ = lean_unsigned_to_nat(2u);
v___x_2198_ = lean_unsigned_to_nat(249u);
v___x_2199_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2200_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2201_ = l_mkPanicMessageWithDecl(v___x_2200_, v___x_2199_, v___x_2198_, v___x_2197_, v___x_2196_);
return v___x_2201_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2205_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2206_ = lean_unsigned_to_nat(34u);
v___x_2207_ = lean_unsigned_to_nat(250u);
v___x_2208_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__0));
v___x_2209_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2210_ = l_mkPanicMessageWithDecl(v___x_2209_, v___x_2208_, v___x_2207_, v___x_2206_, v___x_2205_);
return v___x_2210_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg(lean_object* v_c_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_discr_2218_; lean_object* v_alts_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2288_; 
v_discr_2218_ = lean_ctor_get(v_c_2211_, 2);
v_alts_2219_ = lean_ctor_get(v_c_2211_, 3);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_c_2211_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; lean_object* v_unused_2290_; 
v_unused_2289_ = lean_ctor_get(v_c_2211_, 1);
lean_dec(v_unused_2289_);
v_unused_2290_ = lean_ctor_get(v_c_2211_, 0);
lean_dec(v_unused_2290_);
v___x_2221_ = v_c_2211_;
v_isShared_2222_ = v_isSharedCheck_2288_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_alts_2219_);
lean_inc(v_discr_2218_);
lean_dec(v_c_2211_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2288_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; 
v___x_2223_ = lean_array_get_size(v_alts_2219_);
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_nat_dec_eq(v___x_2223_, v___x_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_del_object(v___x_2221_);
lean_dec_ref(v_alts_2219_);
lean_dec(v_discr_2218_);
v___x_2226_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__1);
v___x_2227_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2226_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = lean_array_get(v___x_2228_, v_alts_2219_, v___x_2229_);
lean_dec_ref(v_alts_2219_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_params_2231_; lean_object* v_code_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2284_; 
v_params_2231_ = lean_ctor_get(v___x_2230_, 1);
v_code_2232_ = lean_ctor_get(v___x_2230_, 2);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v___x_2230_, 0);
lean_dec(v_unused_2285_);
v___x_2234_ = v___x_2230_;
v_isShared_2235_ = v_isSharedCheck_2284_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_code_2232_);
lean_inc(v_params_2231_);
lean_dec(v___x_2230_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2284_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = 0;
v___x_2237_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2238_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2236_, v_params_2231_, v_a_2214_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2239_; lean_object* v_fvarId_2240_; lean_object* v_binderName_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
lean_dec_ref_known(v___x_2238_, 1);
v___x_2239_ = lean_array_get(v___x_2237_, v_params_2231_, v___x_2229_);
lean_dec_ref(v_params_2231_);
v_fvarId_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_fvarId_2240_);
v_binderName_2241_ = lean_ctor_get(v___x_2239_, 1);
lean_inc(v_binderName_2241_);
lean_dec(v___x_2239_);
v___x_2242_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2243_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__3));
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_discr_2218_);
v___x_2246_ = lean_mk_empty_array_with_capacity(v___x_2224_);
v___x_2247_ = lean_array_push(v___x_2246_, v___x_2245_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set_tag(v___x_2234_, 3);
lean_ctor_set(v___x_2234_, 2, v___x_2247_);
lean_ctor_set(v___x_2234_, 1, v___x_2244_);
lean_ctor_set(v___x_2234_, 0, v___x_2243_);
v___x_2249_ = v___x_2234_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2243_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2244_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 3, v___x_2249_);
lean_ctor_set(v___x_2221_, 2, v___x_2242_);
lean_ctor_set(v___x_2221_, 1, v_binderName_2241_);
lean_ctor_set(v___x_2221_, 0, v_fvarId_2240_);
v___x_2251_ = v___x_2221_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_fvarId_2240_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_binderName_2241_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; lean_object* v_lctx_2253_; lean_object* v_nextIdx_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2273_; 
v___x_2252_ = lean_st_ref_take(v_a_2214_);
v_lctx_2253_ = lean_ctor_get(v___x_2252_, 0);
v_nextIdx_2254_ = lean_ctor_get(v___x_2252_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2256_ = v___x_2252_;
v_isShared_2257_ = v_isSharedCheck_2273_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_nextIdx_2254_);
lean_inc(v_lctx_2253_);
lean_dec(v___x_2252_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2273_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
lean_inc_ref(v___x_2251_);
v___x_2258_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2236_, v_lctx_2253_, v___x_2251_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2258_);
v___x_2260_ = v___x_2256_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2258_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_nextIdx_2254_);
v___x_2260_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = lean_st_ref_put(v_a_2214_, v___x_2260_);
v___x_2262_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2232_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2251_);
lean_ctor_set(v___x_2267_, 1, v_a_2263_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
else
{
lean_dec_ref(v___x_2251_);
return v___x_2262_;
}
}
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2234_);
lean_dec_ref(v_code_2232_);
lean_dec_ref(v_params_2231_);
lean_del_object(v___x_2221_);
lean_dec(v_discr_2218_);
v_a_2276_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2238_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2238_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v___x_2230_);
lean_del_object(v___x_2221_);
lean_dec(v_discr_2218_);
v___x_2286_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatToMono___redArg___closed__4);
v___x_2287_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2286_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesFloatToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2211_ = stack[0].m_obj;
lean_object* v_a_2212_ = stack[1].m_obj;
lean_object* v_a_2213_ = stack[2].m_obj;
lean_object* v_a_2214_ = stack[3].m_obj;
lean_object* v_a_2215_ = stack[4].m_obj;
lean_object* v_a_2216_ = stack[5].m_obj;
lean_object* v_res_2291_;
v_res_2291_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
stack->m_obj
 = v_res_2291_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2293_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2294_ = lean_unsigned_to_nat(2u);
v___x_2295_ = lean_unsigned_to_nat(238u);
v___x_2296_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2297_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2298_ = l_mkPanicMessageWithDecl(v___x_2297_, v___x_2296_, v___x_2295_, v___x_2294_, v___x_2293_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2303_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2304_ = lean_unsigned_to_nat(34u);
v___x_2305_ = lean_unsigned_to_nat(239u);
v___x_2306_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__0));
v___x_2307_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2308_ = l_mkPanicMessageWithDecl(v___x_2307_, v___x_2306_, v___x_2305_, v___x_2304_, v___x_2303_);
return v___x_2308_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg(lean_object* v_c_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_discr_2316_; lean_object* v_alts_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2386_; 
v_discr_2316_ = lean_ctor_get(v_c_2309_, 2);
v_alts_2317_ = lean_ctor_get(v_c_2309_, 3);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_c_2309_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2387_ = lean_ctor_get(v_c_2309_, 1);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_c_2309_, 0);
lean_dec(v_unused_2388_);
v___x_2319_ = v_c_2309_;
v_isShared_2320_ = v_isSharedCheck_2386_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_alts_2317_);
lean_inc(v_discr_2316_);
lean_dec(v_c_2309_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2386_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2321_ = lean_array_get_size(v_alts_2317_);
v___x_2322_ = lean_unsigned_to_nat(1u);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_del_object(v___x_2319_);
lean_dec_ref(v_alts_2317_);
lean_dec(v_discr_2316_);
v___x_2324_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__1);
v___x_2325_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2324_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2325_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = lean_array_get(v___x_2326_, v_alts_2317_, v___x_2327_);
lean_dec_ref(v_alts_2317_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_params_2329_; lean_object* v_code_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2382_; 
v_params_2329_ = lean_ctor_get(v___x_2328_, 1);
v_code_2330_ = lean_ctor_get(v___x_2328_, 2);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2382_ == 0)
{
lean_object* v_unused_2383_; 
v_unused_2383_ = lean_ctor_get(v___x_2328_, 0);
lean_dec(v_unused_2383_);
v___x_2332_ = v___x_2328_;
v_isShared_2333_ = v_isSharedCheck_2382_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_code_2330_);
lean_inc(v_params_2329_);
lean_dec(v___x_2328_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2382_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
uint8_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = 0;
v___x_2335_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2336_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2334_, v_params_2329_, v_a_2312_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; lean_object* v_fvarId_2338_; lean_object* v_binderName_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec_ref_known(v___x_2336_, 1);
v___x_2337_ = lean_array_get(v___x_2335_, v_params_2329_, v___x_2327_);
lean_dec_ref(v_params_2329_);
v_fvarId_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_fvarId_2338_);
v_binderName_2339_ = lean_ctor_get(v___x_2337_, 1);
lean_inc(v_binderName_2339_);
lean_dec(v___x_2337_);
v___x_2340_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2341_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__4));
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_discr_2316_);
v___x_2344_ = lean_mk_empty_array_with_capacity(v___x_2322_);
v___x_2345_ = lean_array_push(v___x_2344_, v___x_2343_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 3);
lean_ctor_set(v___x_2332_, 2, v___x_2345_);
lean_ctor_set(v___x_2332_, 1, v___x_2342_);
lean_ctor_set(v___x_2332_, 0, v___x_2341_);
v___x_2347_ = v___x_2332_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 3, v___x_2347_);
lean_ctor_set(v___x_2319_, 2, v___x_2340_);
lean_ctor_set(v___x_2319_, 1, v_binderName_2339_);
lean_ctor_set(v___x_2319_, 0, v_fvarId_2338_);
v___x_2349_ = v___x_2319_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_fvarId_2338_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_binderName_2339_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v_lctx_2351_; lean_object* v_nextIdx_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2371_; 
v___x_2350_ = lean_st_ref_take(v_a_2312_);
v_lctx_2351_ = lean_ctor_get(v___x_2350_, 0);
v_nextIdx_2352_ = lean_ctor_get(v___x_2350_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2354_ = v___x_2350_;
v_isShared_2355_ = v_isSharedCheck_2371_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_nextIdx_2352_);
lean_inc(v_lctx_2351_);
lean_dec(v___x_2350_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2371_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
lean_inc_ref(v___x_2349_);
v___x_2356_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2334_, v_lctx_2351_, v___x_2349_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_nextIdx_2352_);
v___x_2358_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_st_ref_put(v_a_2312_, v___x_2358_);
v___x_2360_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2330_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2369_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2363_ = v___x_2360_;
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2349_);
lean_ctor_set(v___x_2365_, 1, v_a_2361_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2365_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_dec_ref(v___x_2349_);
return v___x_2360_;
}
}
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_del_object(v___x_2332_);
lean_dec_ref(v_code_2330_);
lean_dec_ref(v_params_2329_);
lean_del_object(v___x_2319_);
lean_dec(v_discr_2316_);
v_a_2374_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2336_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2336_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec(v___x_2328_);
lean_del_object(v___x_2319_);
lean_dec(v_discr_2316_);
v___x_2384_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesStringToMono___redArg___closed__5);
v___x_2385_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2384_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2385_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesStringToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2309_ = stack[0].m_obj;
lean_object* v_a_2310_ = stack[1].m_obj;
lean_object* v_a_2311_ = stack[2].m_obj;
lean_object* v_a_2312_ = stack[3].m_obj;
lean_object* v_a_2313_ = stack[4].m_obj;
lean_object* v_a_2314_ = stack[5].m_obj;
lean_object* v_res_2389_;
v_res_2389_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
stack->m_obj
 = v_res_2389_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2391_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2392_ = lean_unsigned_to_nat(2u);
v___x_2393_ = lean_unsigned_to_nat(227u);
v___x_2394_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2395_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2396_ = l_mkPanicMessageWithDecl(v___x_2395_, v___x_2394_, v___x_2393_, v___x_2392_, v___x_2391_);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2401_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2402_ = lean_unsigned_to_nat(34u);
v___x_2403_ = lean_unsigned_to_nat(228u);
v___x_2404_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__0));
v___x_2405_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2406_ = l_mkPanicMessageWithDecl(v___x_2405_, v___x_2404_, v___x_2403_, v___x_2402_, v___x_2401_);
return v___x_2406_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(lean_object* v_c_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_discr_2414_; lean_object* v_alts_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2484_; 
v_discr_2414_ = lean_ctor_get(v_c_2407_, 2);
v_alts_2415_ = lean_ctor_get(v_c_2407_, 3);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_c_2407_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; lean_object* v_unused_2486_; 
v_unused_2485_ = lean_ctor_get(v_c_2407_, 1);
lean_dec(v_unused_2485_);
v_unused_2486_ = lean_ctor_get(v_c_2407_, 0);
lean_dec(v_unused_2486_);
v___x_2417_ = v_c_2407_;
v_isShared_2418_ = v_isSharedCheck_2484_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_alts_2415_);
lean_inc(v_discr_2414_);
lean_dec(v_c_2407_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2484_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2419_ = lean_array_get_size(v_alts_2415_);
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_nat_dec_eq(v___x_2419_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_del_object(v___x_2417_);
lean_dec_ref(v_alts_2415_);
lean_dec(v_discr_2414_);
v___x_2422_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__1);
v___x_2423_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2422_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_array_get(v___x_2424_, v_alts_2415_, v___x_2425_);
lean_dec_ref(v_alts_2415_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_params_2427_; lean_object* v_code_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2480_; 
v_params_2427_ = lean_ctor_get(v___x_2426_, 1);
v_code_2428_ = lean_ctor_get(v___x_2426_, 2);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v___x_2426_, 0);
lean_dec(v_unused_2481_);
v___x_2430_ = v___x_2426_;
v_isShared_2431_ = v_isSharedCheck_2480_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_code_2428_);
lean_inc(v_params_2427_);
lean_dec(v___x_2426_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2480_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = 0;
v___x_2433_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2434_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2432_, v_params_2427_, v_a_2410_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v___x_2435_; lean_object* v_fvarId_2436_; lean_object* v_binderName_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
lean_dec_ref_known(v___x_2434_, 1);
v___x_2435_ = lean_array_get(v___x_2433_, v_params_2427_, v___x_2425_);
lean_dec_ref(v_params_2427_);
v_fvarId_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_fvarId_2436_);
v_binderName_2437_ = lean_ctor_get(v___x_2435_, 1);
lean_inc(v_binderName_2437_);
lean_dec(v___x_2435_);
v___x_2438_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2439_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__3));
v___x_2440_ = lean_box(0);
v___x_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2441_, 0, v_discr_2414_);
v___x_2442_ = lean_mk_empty_array_with_capacity(v___x_2420_);
v___x_2443_ = lean_array_push(v___x_2442_, v___x_2441_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 3);
lean_ctor_set(v___x_2430_, 2, v___x_2443_);
lean_ctor_set(v___x_2430_, 1, v___x_2440_);
lean_ctor_set(v___x_2430_, 0, v___x_2439_);
v___x_2445_ = v___x_2430_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2447_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 3, v___x_2445_);
lean_ctor_set(v___x_2417_, 2, v___x_2438_);
lean_ctor_set(v___x_2417_, 1, v_binderName_2437_);
lean_ctor_set(v___x_2417_, 0, v_fvarId_2436_);
v___x_2447_ = v___x_2417_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fvarId_2436_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_binderName_2437_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v_lctx_2449_; lean_object* v_nextIdx_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2469_; 
v___x_2448_ = lean_st_ref_take(v_a_2410_);
v_lctx_2449_ = lean_ctor_get(v___x_2448_, 0);
v_nextIdx_2450_ = lean_ctor_get(v___x_2448_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2452_ = v___x_2448_;
v_isShared_2453_ = v_isSharedCheck_2469_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_nextIdx_2450_);
lean_inc(v_lctx_2449_);
lean_dec(v___x_2448_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2469_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_inc_ref(v___x_2447_);
v___x_2454_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2432_, v_lctx_2449_, v___x_2447_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2454_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_nextIdx_2450_);
v___x_2456_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_st_ref_put(v_a_2410_, v___x_2456_);
v___x_2458_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2428_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2467_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2467_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2447_);
lean_ctor_set(v___x_2463_, 1, v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2463_);
v___x_2465_ = v___x_2461_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_dec_ref(v___x_2447_);
return v___x_2458_;
}
}
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_del_object(v___x_2430_);
lean_dec_ref(v_code_2428_);
lean_dec_ref(v_params_2427_);
lean_del_object(v___x_2417_);
lean_dec(v_discr_2414_);
v_a_2472_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2434_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2434_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
else
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v___x_2426_);
lean_del_object(v___x_2417_);
lean_dec(v_discr_2414_);
v___x_2482_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4, &l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___closed__4);
v___x_2483_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2482_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
return v___x_2483_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2407_ = stack[0].m_obj;
lean_object* v_a_2408_ = stack[1].m_obj;
lean_object* v_a_2409_ = stack[2].m_obj;
lean_object* v_a_2410_ = stack[3].m_obj;
lean_object* v_a_2411_ = stack[4].m_obj;
lean_object* v_a_2412_ = stack[5].m_obj;
lean_object* v_res_2487_;
v_res_2487_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
stack->m_obj
 = v_res_2487_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2489_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2490_ = lean_unsigned_to_nat(2u);
v___x_2491_ = lean_unsigned_to_nat(215u);
v___x_2492_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2493_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2494_ = l_mkPanicMessageWithDecl(v___x_2493_, v___x_2492_, v___x_2491_, v___x_2490_, v___x_2489_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2498_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2499_ = lean_unsigned_to_nat(34u);
v___x_2500_ = lean_unsigned_to_nat(216u);
v___x_2501_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__0));
v___x_2502_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2503_ = l_mkPanicMessageWithDecl(v___x_2502_, v___x_2501_, v___x_2500_, v___x_2499_, v___x_2498_);
return v___x_2503_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(lean_object* v_c_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v_discr_2511_; lean_object* v_alts_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2581_; 
v_discr_2511_ = lean_ctor_get(v_c_2504_, 2);
v_alts_2512_ = lean_ctor_get(v_c_2504_, 3);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_c_2504_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; lean_object* v_unused_2583_; 
v_unused_2582_ = lean_ctor_get(v_c_2504_, 1);
lean_dec(v_unused_2582_);
v_unused_2583_ = lean_ctor_get(v_c_2504_, 0);
lean_dec(v_unused_2583_);
v___x_2514_ = v_c_2504_;
v_isShared_2515_ = v_isSharedCheck_2581_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_alts_2512_);
lean_inc(v_discr_2511_);
lean_dec(v_c_2504_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2581_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = lean_array_get_size(v_alts_2512_);
v___x_2517_ = lean_unsigned_to_nat(1u);
v___x_2518_ = lean_nat_dec_eq(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_del_object(v___x_2514_);
lean_dec_ref(v_alts_2512_);
lean_dec(v_discr_2511_);
v___x_2519_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__1);
v___x_2520_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2519_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2520_;
}
else
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get(v___x_2521_, v_alts_2512_, v___x_2522_);
lean_dec_ref(v_alts_2512_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_params_2524_; lean_object* v_code_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2577_; 
v_params_2524_ = lean_ctor_get(v___x_2523_, 1);
v_code_2525_ = lean_ctor_get(v___x_2523_, 2);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2578_);
v___x_2527_ = v___x_2523_;
v_isShared_2528_ = v_isSharedCheck_2577_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_code_2525_);
lean_inc(v_params_2524_);
lean_dec(v___x_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2577_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
uint8_t v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = 0;
v___x_2530_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2531_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2529_, v_params_2524_, v_a_2507_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; lean_object* v_fvarId_2533_; lean_object* v_binderName_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_dec_ref_known(v___x_2531_, 1);
v___x_2532_ = lean_array_get(v___x_2530_, v_params_2524_, v___x_2522_);
lean_dec_ref(v_params_2524_);
v_fvarId_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_fvarId_2533_);
v_binderName_2534_ = lean_ctor_get(v___x_2532_, 1);
lean_inc(v_binderName_2534_);
lean_dec(v___x_2532_);
v___x_2535_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2536_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__4));
v___x_2537_ = lean_box(0);
v___x_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_discr_2511_);
v___x_2539_ = lean_mk_empty_array_with_capacity(v___x_2517_);
v___x_2540_ = lean_array_push(v___x_2539_, v___x_2538_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 3);
lean_ctor_set(v___x_2527_, 2, v___x_2540_);
lean_ctor_set(v___x_2527_, 1, v___x_2537_);
lean_ctor_set(v___x_2527_, 0, v___x_2536_);
v___x_2542_ = v___x_2527_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2536_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 3, v___x_2542_);
lean_ctor_set(v___x_2514_, 2, v___x_2535_);
lean_ctor_set(v___x_2514_, 1, v_binderName_2534_);
lean_ctor_set(v___x_2514_, 0, v_fvarId_2533_);
v___x_2544_ = v___x_2514_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_fvarId_2533_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_binderName_2534_);
lean_ctor_set(v_reuseFailAlloc_2567_, 2, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2567_, 3, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v_lctx_2546_; lean_object* v_nextIdx_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2566_; 
v___x_2545_ = lean_st_ref_take(v_a_2507_);
v_lctx_2546_ = lean_ctor_get(v___x_2545_, 0);
v_nextIdx_2547_ = lean_ctor_get(v___x_2545_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2549_ = v___x_2545_;
v_isShared_2550_ = v_isSharedCheck_2566_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_nextIdx_2547_);
lean_inc(v_lctx_2546_);
lean_dec(v___x_2545_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2566_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
lean_inc_ref(v___x_2544_);
v___x_2551_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2529_, v_lctx_2546_, v___x_2544_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_nextIdx_2547_);
v___x_2553_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_st_ref_put(v_a_2507_, v___x_2553_);
v___x_2555_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2525_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2564_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2564_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2544_);
lean_ctor_set(v___x_2560_, 1, v_a_2556_);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2560_);
v___x_2562_ = v___x_2558_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_dec_ref(v___x_2544_);
return v___x_2555_;
}
}
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_del_object(v___x_2527_);
lean_dec_ref(v_code_2525_);
lean_dec_ref(v_params_2524_);
lean_del_object(v___x_2514_);
lean_dec(v_discr_2511_);
v_a_2569_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2531_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2531_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v___x_2523_);
lean_del_object(v___x_2514_);
lean_dec(v_discr_2511_);
v___x_2579_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___closed__5);
v___x_2580_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2579_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2504_ = stack[0].m_obj;
lean_object* v_a_2505_ = stack[1].m_obj;
lean_object* v_a_2506_ = stack[2].m_obj;
lean_object* v_a_2507_ = stack[3].m_obj;
lean_object* v_a_2508_ = stack[4].m_obj;
lean_object* v_a_2509_ = stack[5].m_obj;
lean_object* v_res_2584_;
v_res_2584_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
stack->m_obj
 = v_res_2584_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2586_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2587_ = lean_unsigned_to_nat(2u);
v___x_2588_ = lean_unsigned_to_nat(203u);
v___x_2589_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2590_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2591_ = l_mkPanicMessageWithDecl(v___x_2590_, v___x_2589_, v___x_2588_, v___x_2587_, v___x_2586_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2596_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2597_ = lean_unsigned_to_nat(34u);
v___x_2598_ = lean_unsigned_to_nat(204u);
v___x_2599_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__0));
v___x_2600_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2601_ = l_mkPanicMessageWithDecl(v___x_2600_, v___x_2599_, v___x_2598_, v___x_2597_, v___x_2596_);
return v___x_2601_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg(lean_object* v_c_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_discr_2609_; lean_object* v_alts_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2679_; 
v_discr_2609_ = lean_ctor_get(v_c_2602_, 2);
v_alts_2610_ = lean_ctor_get(v_c_2602_, 3);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_c_2602_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2680_ = lean_ctor_get(v_c_2602_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_c_2602_, 0);
lean_dec(v_unused_2681_);
v___x_2612_ = v_c_2602_;
v_isShared_2613_ = v_isSharedCheck_2679_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_alts_2610_);
lean_inc(v_discr_2609_);
lean_dec(v_c_2602_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2679_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2614_ = lean_array_get_size(v_alts_2610_);
v___x_2615_ = lean_unsigned_to_nat(1u);
v___x_2616_ = lean_nat_dec_eq(v___x_2614_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_del_object(v___x_2612_);
lean_dec_ref(v_alts_2610_);
lean_dec(v_discr_2609_);
v___x_2617_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__1);
v___x_2618_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2617_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get(v___x_2619_, v_alts_2610_, v___x_2620_);
lean_dec_ref(v_alts_2610_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_params_2622_; lean_object* v_code_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2675_; 
v_params_2622_ = lean_ctor_get(v___x_2621_, 1);
v_code_2623_ = lean_ctor_get(v___x_2621_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v___x_2621_, 0);
lean_dec(v_unused_2676_);
v___x_2625_ = v___x_2621_;
v_isShared_2626_ = v_isSharedCheck_2675_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_code_2623_);
lean_inc(v_params_2622_);
lean_dec(v___x_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2675_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint8_t v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = 0;
v___x_2628_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2629_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2627_, v_params_2622_, v_a_2605_);
if (lean_obj_tag(v___x_2629_) == 0)
{
lean_object* v___x_2630_; lean_object* v_fvarId_2631_; lean_object* v_binderName_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec_ref_known(v___x_2629_, 1);
v___x_2630_ = lean_array_get(v___x_2628_, v_params_2622_, v___x_2620_);
lean_dec_ref(v_params_2622_);
v_fvarId_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_fvarId_2631_);
v_binderName_2632_ = lean_ctor_get(v___x_2630_, 1);
lean_inc(v_binderName_2632_);
lean_dec(v___x_2630_);
v___x_2633_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2634_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__4));
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_discr_2609_);
v___x_2637_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__5);
v___x_2638_ = lean_array_push(v___x_2637_, v___x_2636_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set_tag(v___x_2625_, 3);
lean_ctor_set(v___x_2625_, 2, v___x_2638_);
lean_ctor_set(v___x_2625_, 1, v___x_2635_);
lean_ctor_set(v___x_2625_, 0, v___x_2634_);
v___x_2640_ = v___x_2625_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2634_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 3, v___x_2640_);
lean_ctor_set(v___x_2612_, 2, v___x_2633_);
lean_ctor_set(v___x_2612_, 1, v_binderName_2632_);
lean_ctor_set(v___x_2612_, 0, v_fvarId_2631_);
v___x_2642_ = v___x_2612_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_fvarId_2631_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_binderName_2632_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v___x_2633_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v___x_2640_);
v___x_2642_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2643_; lean_object* v_lctx_2644_; lean_object* v_nextIdx_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2664_; 
v___x_2643_ = lean_st_ref_take(v_a_2605_);
v_lctx_2644_ = lean_ctor_get(v___x_2643_, 0);
v_nextIdx_2645_ = lean_ctor_get(v___x_2643_, 1);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2647_ = v___x_2643_;
v_isShared_2648_ = v_isSharedCheck_2664_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_nextIdx_2645_);
lean_inc(v_lctx_2644_);
lean_dec(v___x_2643_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2664_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_inc_ref(v___x_2642_);
v___x_2649_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2627_, v_lctx_2644_, v___x_2642_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 0, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_nextIdx_2645_);
v___x_2651_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_st_ref_put(v_a_2605_, v___x_2651_);
v___x_2653_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2623_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2642_);
lean_ctor_set(v___x_2658_, 1, v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
else
{
lean_dec_ref(v___x_2642_);
return v___x_2653_;
}
}
}
}
}
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_del_object(v___x_2625_);
lean_dec_ref(v_code_2623_);
lean_dec_ref(v_params_2622_);
lean_del_object(v___x_2612_);
lean_dec(v_discr_2609_);
v_a_2667_ = lean_ctor_get(v___x_2629_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2629_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2629_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec(v___x_2621_);
lean_del_object(v___x_2612_);
lean_dec(v_discr_2609_);
v___x_2677_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesArrayToMono___redArg___closed__6);
v___x_2678_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2677_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
return v___x_2678_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesArrayToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2602_ = stack[0].m_obj;
lean_object* v_a_2603_ = stack[1].m_obj;
lean_object* v_a_2604_ = stack[2].m_obj;
lean_object* v_a_2605_ = stack[3].m_obj;
lean_object* v_a_2606_ = stack[4].m_obj;
lean_object* v_a_2607_ = stack[5].m_obj;
lean_object* v_res_2682_;
v_res_2682_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
stack->m_obj
 = v_res_2682_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2684_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__1));
v___x_2685_ = lean_unsigned_to_nat(2u);
v___x_2686_ = lean_unsigned_to_nat(192u);
v___x_2687_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2688_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2689_ = l_mkPanicMessageWithDecl(v___x_2688_, v___x_2687_, v___x_2686_, v___x_2685_, v___x_2684_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2691_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__12));
v___x_2692_ = lean_unsigned_to_nat(34u);
v___x_2693_ = lean_unsigned_to_nat(193u);
v___x_2694_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__0));
v___x_2695_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__10));
v___x_2696_ = l_mkPanicMessageWithDecl(v___x_2695_, v___x_2694_, v___x_2693_, v___x_2692_, v___x_2691_);
return v___x_2696_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg(lean_object* v_c_2697_, lean_object* v_uintName_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_discr_2705_; lean_object* v_alts_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2776_; 
v_discr_2705_ = lean_ctor_get(v_c_2697_, 2);
v_alts_2706_ = lean_ctor_get(v_c_2697_, 3);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_c_2697_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; lean_object* v_unused_2778_; 
v_unused_2777_ = lean_ctor_get(v_c_2697_, 1);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_c_2697_, 0);
lean_dec(v_unused_2778_);
v___x_2708_ = v_c_2697_;
v_isShared_2709_ = v_isSharedCheck_2776_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_alts_2706_);
lean_inc(v_discr_2705_);
lean_dec(v_c_2697_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2776_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2710_ = lean_array_get_size(v_alts_2706_);
v___x_2711_ = lean_unsigned_to_nat(1u);
v___x_2712_ = lean_nat_dec_eq(v___x_2710_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_del_object(v___x_2708_);
lean_dec_ref(v_alts_2706_);
lean_dec(v_discr_2705_);
lean_dec(v_uintName_2698_);
v___x_2713_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__2);
v___x_2714_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2713_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2714_;
}
else
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0, &l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0_once, _init_l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__4___closed__0);
v___x_2716_ = lean_unsigned_to_nat(0u);
v___x_2717_ = lean_array_get(v___x_2715_, v_alts_2706_, v___x_2716_);
lean_dec_ref(v_alts_2706_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_params_2718_; lean_object* v_code_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2772_; 
v_params_2718_ = lean_ctor_get(v___x_2717_, 1);
v_code_2719_ = lean_ctor_get(v___x_2717_, 2);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2772_ == 0)
{
lean_object* v_unused_2773_; 
v_unused_2773_ = lean_ctor_get(v___x_2717_, 0);
lean_dec(v_unused_2773_);
v___x_2721_ = v___x_2717_;
v_isShared_2722_ = v_isSharedCheck_2772_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_code_2719_);
lean_inc(v_params_2718_);
lean_dec(v___x_2717_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2772_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
uint8_t v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = 0;
v___x_2724_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2725_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2723_, v_params_2718_, v_a_2701_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v___x_2726_; lean_object* v_fvarId_2727_; lean_object* v_binderName_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
lean_dec_ref_known(v___x_2725_, 1);
v___x_2726_ = lean_array_get(v___x_2724_, v_params_2718_, v___x_2716_);
lean_dec_ref(v_params_2718_);
v_fvarId_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_fvarId_2727_);
v_binderName_2728_ = lean_ctor_get(v___x_2726_, 1);
lean_inc(v_binderName_2728_);
lean_dec(v___x_2726_);
v___x_2729_ = l_Lean_Compiler_LCNF_anyExpr;
v___x_2730_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__4));
v___x_2731_ = l_Lean_Name_str___override(v_uintName_2698_, v___x_2730_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_discr_2705_);
v___x_2734_ = lean_mk_empty_array_with_capacity(v___x_2711_);
v___x_2735_ = lean_array_push(v___x_2734_, v___x_2733_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 3);
lean_ctor_set(v___x_2721_, 2, v___x_2735_);
lean_ctor_set(v___x_2721_, 1, v___x_2732_);
lean_ctor_set(v___x_2721_, 0, v___x_2731_);
v___x_2737_ = v___x_2721_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2732_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2739_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 3, v___x_2737_);
lean_ctor_set(v___x_2708_, 2, v___x_2729_);
lean_ctor_set(v___x_2708_, 1, v_binderName_2728_);
lean_ctor_set(v___x_2708_, 0, v_fvarId_2727_);
v___x_2739_ = v___x_2708_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_fvarId_2727_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_binderName_2728_);
lean_ctor_set(v_reuseFailAlloc_2762_, 2, v___x_2729_);
lean_ctor_set(v_reuseFailAlloc_2762_, 3, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v_lctx_2741_; lean_object* v_nextIdx_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2761_; 
v___x_2740_ = lean_st_ref_take(v_a_2701_);
v_lctx_2741_ = lean_ctor_get(v___x_2740_, 0);
v_nextIdx_2742_ = lean_ctor_get(v___x_2740_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2744_ = v___x_2740_;
v_isShared_2745_ = v_isSharedCheck_2761_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_nextIdx_2742_);
lean_inc(v_lctx_2741_);
lean_dec(v___x_2740_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2761_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_inc_ref(v___x_2739_);
v___x_2746_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2723_, v_lctx_2741_, v___x_2739_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set(v___x_2744_, 0, v___x_2746_);
v___x_2748_ = v___x_2744_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v_nextIdx_2742_);
v___x_2748_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_st_ref_put(v_a_2701_, v___x_2748_);
v___x_2750_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2719_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2759_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2759_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2739_);
lean_ctor_set(v___x_2755_, 1, v_a_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2755_);
v___x_2757_ = v___x_2753_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
else
{
lean_dec_ref(v___x_2739_);
return v___x_2750_;
}
}
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_del_object(v___x_2721_);
lean_dec_ref(v_code_2719_);
lean_dec_ref(v_params_2718_);
lean_del_object(v___x_2708_);
lean_dec(v_discr_2705_);
lean_dec(v_uintName_2698_);
v_a_2764_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2725_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2725_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v___x_2717_);
lean_del_object(v___x_2708_);
lean_dec(v_discr_2705_);
lean_dec(v_uintName_2698_);
v___x_2774_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__5);
v___x_2775_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_2774_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2775_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesUIntToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2697_ = stack[0].m_obj;
lean_object* v_uintName_2698_ = stack[1].m_obj;
lean_object* v_a_2699_ = stack[2].m_obj;
lean_object* v_a_2700_ = stack[3].m_obj;
lean_object* v_a_2701_ = stack[4].m_obj;
lean_object* v_a_2702_ = stack[5].m_obj;
lean_object* v_a_2703_ = stack[6].m_obj;
lean_object* v_res_2779_;
v_res_2779_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_2697_, v_uintName_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
stack->m_obj
 = v_res_2779_;
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_2782_ = l_Lean_mkConst(v___x_2781_, v___x_2780_);
return v___x_2782_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2789_ = lean_box(0);
v___x_2790_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_2791_ = l_Lean_mkConst(v___x_2790_, v___x_2789_);
return v___x_2791_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2802_ = lean_box(0);
v___x_2803_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_2804_ = l_Lean_mkConst(v___x_2803_, v___x_2802_);
return v___x_2804_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(lean_object* v___x_2837_, size_t v_sz_2838_, size_t v_i_2839_, lean_object* v_bs_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = lean_usize_dec_lt(v_i_2839_, v_sz_2838_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; 
lean_dec(v___x_2837_);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_bs_2840_);
return v___x_2848_;
}
else
{
lean_object* v_v_2849_; lean_object* v___x_2850_; lean_object* v_bs_x27_2851_; lean_object* v_a_2853_; 
v_v_2849_ = lean_array_uget(v_bs_2840_, v_i_2839_);
v___x_2850_ = lean_unsigned_to_nat(0u);
v_bs_x27_2851_ = lean_array_uset(v_bs_2840_, v_i_2839_, v___x_2850_);
if (lean_obj_tag(v_v_2849_) == 0)
{
lean_object* v_ctorName_2858_; lean_object* v_params_2859_; lean_object* v_code_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2987_; 
v_ctorName_2858_ = lean_ctor_get(v_v_2849_, 0);
v_params_2859_ = lean_ctor_get(v_v_2849_, 1);
v_code_2860_ = lean_ctor_get(v_v_2849_, 2);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_v_2849_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2862_ = v_v_2849_;
v_isShared_2863_ = v_isSharedCheck_2987_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_code_2860_);
lean_inc(v_params_2859_);
lean_inc(v_ctorName_2858_);
lean_dec(v_v_2849_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2987_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
uint8_t v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2864_ = 0;
v___x_2865_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_2868_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_2864_, v_params_2859_, v___y_2843_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
lean_dec_ref_known(v___x_2868_, 1);
v___x_2869_ = lean_array_get(v___x_2865_, v_params_2859_, v___x_2850_);
lean_dec_ref(v_params_2859_);
v___x_2870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__1));
v___x_2871_ = lean_name_eq(v_ctorName_2858_, v___x_2870_);
lean_dec(v_ctorName_2858_);
if (v___x_2871_ == 0)
{
lean_object* v_fvarId_2872_; lean_object* v_binderName_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v_lctx_2881_; lean_object* v_nextIdx_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2907_; 
v_fvarId_2872_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_fvarId_2872_);
v_binderName_2873_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_binderName_2873_);
lean_dec(v___x_2869_);
v___x_2874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2875_ = lean_unsigned_to_nat(1u);
v___x_2876_ = lean_mk_empty_array_with_capacity(v___x_2875_);
lean_inc(v___x_2837_);
v___x_2877_ = lean_array_push(v___x_2876_, v___x_2837_);
v___x_2878_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2874_);
lean_ctor_set(v___x_2878_, 1, v___x_2866_);
lean_ctor_set(v___x_2878_, 2, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2879_, 0, v_fvarId_2872_);
lean_ctor_set(v___x_2879_, 1, v_binderName_2873_);
lean_ctor_set(v___x_2879_, 2, v___x_2867_);
lean_ctor_set(v___x_2879_, 3, v___x_2878_);
v___x_2880_ = lean_st_ref_take(v___y_2843_);
v_lctx_2881_ = lean_ctor_get(v___x_2880_, 0);
v_nextIdx_2882_ = lean_ctor_get(v___x_2880_, 1);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2884_ = v___x_2880_;
v_isShared_2885_ = v_isSharedCheck_2907_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_nextIdx_2882_);
lean_inc(v_lctx_2881_);
lean_dec(v___x_2880_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2907_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_inc_ref(v___x_2879_);
v___x_2886_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2864_, v_lctx_2881_, v___x_2879_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2886_);
v___x_2888_ = v___x_2884_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2886_);
lean_ctor_set(v_reuseFailAlloc_2906_, 1, v_nextIdx_2882_);
v___x_2888_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_st_ref_put(v___y_2843_, v___x_2888_);
v___x_2890_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2860_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_2893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2879_);
lean_ctor_set(v___x_2894_, 1, v_a_2891_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 2, v___x_2894_);
lean_ctor_set(v___x_2862_, 1, v___x_2893_);
lean_ctor_set(v___x_2862_, 0, v___x_2892_);
v___x_2896_ = v___x_2862_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2892_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2893_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
v_a_2853_ = v___x_2896_;
goto v___jp_2852_;
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref_known(v___x_2879_, 4);
lean_del_object(v___x_2862_);
lean_dec_ref(v_bs_x27_2851_);
lean_dec(v___x_2837_);
v_a_2898_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2890_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2890_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__5));
v___x_2909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___closed__3));
v___x_2910_ = lean_unsigned_to_nat(1u);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2910_);
lean_inc(v___x_2837_);
v___x_2912_ = lean_array_push(v___x_2911_, v___x_2837_);
v___x_2913_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2909_);
lean_ctor_set(v___x_2913_, 1, v___x_2866_);
lean_ctor_set(v___x_2913_, 2, v___x_2912_);
v___x_2914_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2864_, v___x_2908_, v___x_2867_, v___x_2913_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
v___x_2916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_2917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_2918_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_2864_, v___x_2916_, v___x_2867_, v___x_2917_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v_fvarId_2920_; lean_object* v_binderName_2921_; lean_object* v_fvarId_2922_; lean_object* v_fvarId_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v_lctx_2934_; lean_object* v_nextIdx_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2962_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v_fvarId_2920_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_fvarId_2920_);
v_binderName_2921_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_binderName_2921_);
lean_dec(v___x_2869_);
v_fvarId_2922_ = lean_ctor_get(v_a_2915_, 0);
v_fvarId_2923_ = lean_ctor_get(v_a_2919_, 0);
v___x_2924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_2922_);
v___x_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2925_, 0, v_fvarId_2922_);
lean_inc(v_fvarId_2923_);
v___x_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_fvarId_2923_);
v___x_2927_ = lean_unsigned_to_nat(2u);
v___x_2928_ = lean_mk_empty_array_with_capacity(v___x_2927_);
v___x_2929_ = lean_array_push(v___x_2928_, v___x_2925_);
v___x_2930_ = lean_array_push(v___x_2929_, v___x_2926_);
v___x_2931_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2924_);
lean_ctor_set(v___x_2931_, 1, v___x_2866_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2932_, 0, v_fvarId_2920_);
lean_ctor_set(v___x_2932_, 1, v_binderName_2921_);
lean_ctor_set(v___x_2932_, 2, v___x_2867_);
lean_ctor_set(v___x_2932_, 3, v___x_2931_);
v___x_2933_ = lean_st_ref_take(v___y_2843_);
v_lctx_2934_ = lean_ctor_get(v___x_2933_, 0);
v_nextIdx_2935_ = lean_ctor_get(v___x_2933_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2937_ = v___x_2933_;
v_isShared_2938_ = v_isSharedCheck_2962_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_nextIdx_2935_);
lean_inc(v_lctx_2934_);
lean_dec(v___x_2933_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2962_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_inc_ref(v___x_2932_);
v___x_2939_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_2864_, v_lctx_2934_, v___x_2932_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2939_);
v___x_2941_ = v___x_2937_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_nextIdx_2935_);
v___x_2941_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_st_ref_put(v___y_2843_, v___x_2941_);
v___x_2943_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2860_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_2946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2932_);
lean_ctor_set(v___x_2947_, 1, v_a_2944_);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2919_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v_a_2915_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 2, v___x_2949_);
lean_ctor_set(v___x_2862_, 1, v___x_2946_);
lean_ctor_set(v___x_2862_, 0, v___x_2945_);
v___x_2951_ = v___x_2862_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
v_a_2853_ = v___x_2951_;
goto v___jp_2852_;
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref_known(v___x_2932_, 4);
lean_dec(v_a_2919_);
lean_dec(v_a_2915_);
lean_del_object(v___x_2862_);
lean_dec_ref(v_bs_x27_2851_);
lean_dec(v___x_2837_);
v_a_2953_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2943_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2943_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_a_2915_);
lean_dec(v___x_2869_);
lean_del_object(v___x_2862_);
lean_dec_ref(v_code_2860_);
lean_dec_ref(v_bs_x27_2851_);
lean_dec(v___x_2837_);
v_a_2963_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2918_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2918_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v___x_2869_);
lean_del_object(v___x_2862_);
lean_dec_ref(v_code_2860_);
lean_dec_ref(v_bs_x27_2851_);
lean_dec(v___x_2837_);
v_a_2971_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2914_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2914_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_del_object(v___x_2862_);
lean_dec_ref(v_code_2860_);
lean_dec_ref(v_params_2859_);
lean_dec(v_ctorName_2858_);
lean_dec_ref(v_bs_x27_2851_);
lean_dec(v___x_2837_);
v_a_2979_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2868_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2868_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
else
{
lean_object* v_code_2988_; lean_object* v___x_2989_; 
v_code_2988_ = lean_ctor_get(v_v_2849_, 0);
lean_inc_ref(v_code_2988_);
v___x_2989_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_2988_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_2849_, v_a_2990_);
v_a_2853_ = v___x_2991_;
goto v___jp_2852_;
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref_known(v_v_2849_, 1);
lean_dec_ref(v_bs_x27_2851_);
lean_dec(v___x_2837_);
v_a_2992_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2989_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2989_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
v___jp_2852_:
{
size_t v___x_2854_; size_t v___x_2855_; lean_object* v___x_2856_; 
v___x_2854_ = ((size_t)1ULL);
v___x_2855_ = lean_usize_add(v_i_2839_, v___x_2854_);
v___x_2856_ = lean_array_uset(v_bs_x27_2851_, v_i_2839_, v_a_2853_);
v_i_2839_ = v___x_2855_;
v_bs_2840_ = v___x_2856_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2837_ = stack[0].m_obj;
size_t v_sz_2838_ = stack[1].m_num;
size_t v_i_2839_ = stack[2].m_num;
lean_object* v_bs_2840_ = stack[3].m_obj;
lean_object* v___y_2841_ = stack[4].m_obj;
lean_object* v___y_2842_ = stack[5].m_obj;
lean_object* v___y_2843_ = stack[6].m_obj;
lean_object* v___y_2844_ = stack[7].m_obj;
lean_object* v___y_2845_ = stack[8].m_obj;
lean_object* v_res_3000_;
v_res_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_2837_, v_sz_2838_, v_i_2839_, v_bs_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
stack->m_obj
 = v_res_3000_;
}
lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg(lean_object* v_c_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v_resultType_3008_; lean_object* v_discr_3009_; lean_object* v_alts_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3107_; 
v_resultType_3008_ = lean_ctor_get(v_c_3001_, 1);
v_discr_3009_ = lean_ctor_get(v_c_3001_, 2);
v_alts_3010_ = lean_ctor_get(v_c_3001_, 3);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_c_3001_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_c_3001_, 0);
lean_dec(v_unused_3108_);
v___x_3012_ = v_c_3001_;
v_isShared_3013_ = v_isSharedCheck_3107_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_alts_3010_);
lean_inc(v_discr_3009_);
lean_inc(v_resultType_3008_);
lean_dec(v_c_3001_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3107_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
uint8_t v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = 0;
v___x_3015_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3008_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3019_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__1));
v___x_3020_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_3021_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3014_, v___x_3019_, v___x_3018_, v___x_3020_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v_fvarId_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v_fvarId_3023_ = lean_ctor_get(v_a_3022_, 0);
v___x_3024_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__5));
v___x_3025_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6, &l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__6);
v___x_3026_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__8));
lean_inc(v_fvarId_3023_);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_fvarId_3023_);
v___x_3028_ = lean_unsigned_to_nat(1u);
v___x_3029_ = lean_mk_empty_array_with_capacity(v___x_3028_);
v___x_3030_ = lean_array_push(v___x_3029_, v___x_3027_);
v___x_3031_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3026_);
lean_ctor_set(v___x_3031_, 1, v___x_3017_);
lean_ctor_set(v___x_3031_, 2, v___x_3030_);
v___x_3032_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3014_, v___x_3024_, v___x_3025_, v___x_3031_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v_fvarId_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v_fvarId_3034_ = lean_ctor_get(v_a_3033_, 0);
v___x_3035_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__10));
v___x_3036_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3037_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3038_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__12));
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_discr_3009_);
lean_inc(v_fvarId_3034_);
v___x_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_fvarId_3034_);
v___x_3041_ = lean_unsigned_to_nat(2u);
v___x_3042_ = lean_mk_empty_array_with_capacity(v___x_3041_);
lean_inc_ref(v___x_3039_);
v___x_3043_ = lean_array_push(v___x_3042_, v___x_3039_);
v___x_3044_ = lean_array_push(v___x_3043_, v___x_3040_);
v___x_3045_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3038_);
lean_ctor_set(v___x_3045_, 1, v___x_3017_);
lean_ctor_set(v___x_3045_, 2, v___x_3044_);
v___x_3046_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3014_, v___x_3035_, v___x_3037_, v___x_3045_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; size_t v_sz_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v_sz_3048_ = lean_array_size(v_alts_3010_);
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_3039_, v_sz_3048_, v___x_3049_, v_alts_3010_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3066_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3053_ = v___x_3050_;
v_isShared_3054_ = v_isSharedCheck_3066_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_3050_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3066_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v_fvarId_3055_; lean_object* v___x_3057_; 
v_fvarId_3055_ = lean_ctor_get(v_a_3047_, 0);
lean_inc(v_fvarId_3055_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 3, v_a_3051_);
lean_ctor_set(v___x_3012_, 2, v_fvarId_3055_);
lean_ctor_set(v___x_3012_, 1, v_a_3016_);
lean_ctor_set(v___x_3012_, 0, v___x_3036_);
v___x_3057_ = v___x_3012_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_a_3016_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_fvarId_3055_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v_a_3051_);
v___x_3057_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3058_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3059_, 0, v_a_3047_);
lean_ctor_set(v___x_3059_, 1, v___x_3058_);
v___x_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3060_, 0, v_a_3033_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_a_3022_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 0, v___x_3061_);
v___x_3063_ = v___x_3053_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
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
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_3047_);
lean_dec(v_a_3033_);
lean_dec(v_a_3022_);
lean_dec(v_a_3016_);
lean_del_object(v___x_3012_);
v_a_3067_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3050_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3050_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref_known(v___x_3039_, 1);
lean_dec(v_a_3033_);
lean_dec(v_a_3022_);
lean_dec(v_a_3016_);
lean_del_object(v___x_3012_);
lean_dec_ref(v_alts_3010_);
v_a_3075_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3046_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3046_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec(v_a_3022_);
lean_dec(v_a_3016_);
lean_del_object(v___x_3012_);
lean_dec_ref(v_alts_3010_);
lean_dec(v_discr_3009_);
v_a_3083_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3032_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3032_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_3016_);
lean_del_object(v___x_3012_);
lean_dec_ref(v_alts_3010_);
lean_dec(v_discr_3009_);
v_a_3091_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3021_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3021_);
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
lean_del_object(v___x_3012_);
lean_dec_ref(v_alts_3010_);
lean_dec(v_discr_3009_);
v_a_3099_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3015_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3015_);
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
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesIntToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3001_ = stack[0].m_obj;
lean_object* v_a_3002_ = stack[1].m_obj;
lean_object* v_a_3003_ = stack[2].m_obj;
lean_object* v_a_3004_ = stack[3].m_obj;
lean_object* v_a_3005_ = stack[4].m_obj;
lean_object* v_a_3006_ = stack[5].m_obj;
lean_object* v_res_3109_;
v_res_3109_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_);
stack->m_obj
 = v_res_3109_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(lean_object* v___x_3119_, size_t v_sz_3120_, size_t v_i_3121_, lean_object* v_bs_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_usize_dec_lt(v_i_3121_, v_sz_3120_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; 
lean_dec(v___x_3119_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_bs_3122_);
return v___x_3130_;
}
else
{
lean_object* v_v_3131_; lean_object* v___x_3132_; lean_object* v_bs_x27_3133_; lean_object* v_a_3135_; 
v_v_3131_ = lean_array_uget(v_bs_3122_, v_i_3121_);
v___x_3132_ = lean_unsigned_to_nat(0u);
v_bs_x27_3133_ = lean_array_uset(v_bs_3122_, v_i_3121_, v___x_3132_);
if (lean_obj_tag(v_v_3131_) == 0)
{
lean_object* v_ctorName_3140_; lean_object* v_params_3141_; lean_object* v_code_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3229_; 
v_ctorName_3140_ = lean_ctor_get(v_v_3131_, 0);
v_params_3141_ = lean_ctor_get(v_v_3131_, 1);
v_code_3142_ = lean_ctor_get(v_v_3131_, 2);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_v_3131_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3144_ = v_v_3131_;
v_isShared_3145_ = v_isSharedCheck_3229_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_code_3142_);
lean_inc(v_params_3141_);
lean_inc(v_ctorName_3140_);
lean_dec(v_v_3131_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3229_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
uint8_t v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3146_ = 0;
v___x_3147_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3, &l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_casesUIntToMono___redArg___closed__3);
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3150_ = l_Lean_Compiler_LCNF_eraseParams___redArg(v___x_3146_, v_params_3141_, v___y_3125_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v___x_3151_; uint8_t v___x_3152_; 
lean_dec_ref_known(v___x_3150_, 1);
v___x_3151_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__9));
v___x_3152_ = lean_name_eq(v_ctorName_3140_, v___x_3151_);
lean_dec(v_ctorName_3140_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; 
lean_dec_ref(v_params_3141_);
v___x_3153_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3142_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
v___x_3155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__1));
v___x_3156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 2, v_a_3154_);
lean_ctor_set(v___x_3144_, 1, v___x_3156_);
lean_ctor_set(v___x_3144_, 0, v___x_3155_);
v___x_3158_ = v___x_3144_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_a_3154_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
v_a_3135_ = v___x_3158_;
goto v___jp_3134_;
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_del_object(v___x_3144_);
lean_dec_ref(v_bs_x27_3133_);
lean_dec(v___x_3119_);
v_a_3160_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3153_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3153_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3168_ = lean_array_get(v___x_3147_, v_params_3141_, v___x_3132_);
lean_dec_ref(v_params_3141_);
v___x_3169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__4));
v___x_3170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3171_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3146_, v___x_3169_, v___x_3149_, v___x_3170_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v_fvarId_3173_; lean_object* v_binderName_3174_; lean_object* v_fvarId_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v_lctx_3185_; lean_object* v_nextIdx_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3212_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref_known(v___x_3171_, 1);
v_fvarId_3173_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_fvarId_3173_);
v_binderName_3174_ = lean_ctor_get(v___x_3168_, 1);
lean_inc(v_binderName_3174_);
lean_dec(v___x_3168_);
v_fvarId_3175_ = lean_ctor_get(v_a_3172_, 0);
v___x_3176_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__8));
lean_inc(v_fvarId_3175_);
v___x_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_fvarId_3175_);
v___x_3178_ = lean_unsigned_to_nat(2u);
v___x_3179_ = lean_mk_empty_array_with_capacity(v___x_3178_);
lean_inc(v___x_3119_);
v___x_3180_ = lean_array_push(v___x_3179_, v___x_3119_);
v___x_3181_ = lean_array_push(v___x_3180_, v___x_3177_);
v___x_3182_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3176_);
lean_ctor_set(v___x_3182_, 1, v___x_3148_);
lean_ctor_set(v___x_3182_, 2, v___x_3181_);
v___x_3183_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3183_, 0, v_fvarId_3173_);
lean_ctor_set(v___x_3183_, 1, v_binderName_3174_);
lean_ctor_set(v___x_3183_, 2, v___x_3149_);
lean_ctor_set(v___x_3183_, 3, v___x_3182_);
v___x_3184_ = lean_st_ref_take(v___y_3125_);
v_lctx_3185_ = lean_ctor_get(v___x_3184_, 0);
v_nextIdx_3186_ = lean_ctor_get(v___x_3184_, 1);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3188_ = v___x_3184_;
v_isShared_3189_ = v_isSharedCheck_3212_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_nextIdx_3186_);
lean_inc(v_lctx_3185_);
lean_dec(v___x_3184_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3212_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3190_; lean_object* v___x_3192_; 
lean_inc_ref(v___x_3183_);
v___x_3190_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_3146_, v_lctx_3185_, v___x_3183_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3190_);
v___x_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_nextIdx_3186_);
v___x_3192_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = lean_st_ref_put(v___y_3125_, v___x_3192_);
v___x_3194_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3142_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__10));
v___x_3197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__2));
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3183_);
lean_ctor_set(v___x_3198_, 1, v_a_3195_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_a_3172_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 2, v___x_3199_);
lean_ctor_set(v___x_3144_, 1, v___x_3197_);
lean_ctor_set(v___x_3144_, 0, v___x_3196_);
v___x_3201_ = v___x_3144_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
v_a_3135_ = v___x_3201_;
goto v___jp_3134_;
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec_ref_known(v___x_3183_, 4);
lean_dec(v_a_3172_);
lean_del_object(v___x_3144_);
lean_dec_ref(v_bs_x27_3133_);
lean_dec(v___x_3119_);
v_a_3203_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3194_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3194_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v___x_3168_);
lean_del_object(v___x_3144_);
lean_dec_ref(v_code_3142_);
lean_dec_ref(v_bs_x27_3133_);
lean_dec(v___x_3119_);
v_a_3213_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3171_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3171_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_del_object(v___x_3144_);
lean_dec_ref(v_code_3142_);
lean_dec_ref(v_params_3141_);
lean_dec(v_ctorName_3140_);
lean_dec_ref(v_bs_x27_3133_);
lean_dec(v___x_3119_);
v_a_3221_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3150_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3150_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
else
{
lean_object* v_code_3230_; lean_object* v___x_3231_; 
v_code_3230_ = lean_ctor_get(v_v_3131_, 0);
lean_inc_ref(v_code_3230_);
v___x_3231_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3230_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_v_3131_, v_a_3232_);
v_a_3135_ = v___x_3233_;
goto v___jp_3134_;
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref_known(v_v_3131_, 1);
lean_dec_ref(v_bs_x27_3133_);
lean_dec(v___x_3119_);
v_a_3234_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3231_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3231_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
v___jp_3134_:
{
size_t v___x_3136_; size_t v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = ((size_t)1ULL);
v___x_3137_ = lean_usize_add(v_i_3121_, v___x_3136_);
v___x_3138_ = lean_array_uset(v_bs_x27_3133_, v_i_3121_, v_a_3135_);
v_i_3121_ = v___x_3137_;
v_bs_3122_ = v___x_3138_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3119_ = stack[0].m_obj;
size_t v_sz_3120_ = stack[1].m_num;
size_t v_i_3121_ = stack[2].m_num;
lean_object* v_bs_3122_ = stack[3].m_obj;
lean_object* v___y_3123_ = stack[4].m_obj;
lean_object* v___y_3124_ = stack[5].m_obj;
lean_object* v___y_3125_ = stack[6].m_obj;
lean_object* v___y_3126_ = stack[7].m_obj;
lean_object* v___y_3127_ = stack[8].m_obj;
lean_object* v_res_3242_;
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3119_, v_sz_3120_, v_i_3121_, v_bs_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
stack->m_obj
 = v_res_3242_;
}
lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg(lean_object* v_c_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_resultType_3250_; lean_object* v_discr_3251_; lean_object* v_alts_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3329_; 
v_resultType_3250_ = lean_ctor_get(v_c_3243_, 1);
v_discr_3251_ = lean_ctor_get(v_c_3243_, 2);
v_alts_3252_ = lean_ctor_get(v_c_3243_, 3);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_c_3243_);
if (v_isSharedCheck_3329_ == 0)
{
lean_object* v_unused_3330_; 
v_unused_3330_ = lean_ctor_get(v_c_3243_, 0);
lean_dec(v_unused_3330_);
v___x_3254_ = v_c_3243_;
v_isShared_3255_ = v_isSharedCheck_3329_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_alts_3252_);
lean_inc(v_discr_3251_);
lean_inc(v_resultType_3250_);
lean_dec(v_c_3243_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3329_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
uint8_t v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = 0;
v___x_3257_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3250_, v_a_3247_, v_a_3248_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___x_3257_, 1);
v___x_3259_ = lean_box(0);
v___x_3260_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__1);
v___x_3261_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__2));
v___x_3262_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__15));
v___x_3263_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3256_, v___x_3261_, v___x_3260_, v___x_3262_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v_fvarId_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v_fvarId_3265_ = lean_ctor_get(v_a_3264_, 0);
v___x_3266_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__4));
v___x_3267_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__6));
v___x_3268_ = lean_obj_once(&l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7, &l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7_once, _init_l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__7);
v___x_3269_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__9));
v___x_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_discr_3251_);
lean_inc(v_fvarId_3265_);
v___x_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_fvarId_3265_);
v___x_3272_ = lean_unsigned_to_nat(2u);
v___x_3273_ = lean_mk_empty_array_with_capacity(v___x_3272_);
lean_inc_ref(v___x_3270_);
v___x_3274_ = lean_array_push(v___x_3273_, v___x_3270_);
v___x_3275_ = lean_array_push(v___x_3274_, v___x_3271_);
v___x_3276_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3269_);
lean_ctor_set(v___x_3276_, 1, v___x_3259_);
lean_ctor_set(v___x_3276_, 2, v___x_3275_);
v___x_3277_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_3256_, v___x_3266_, v___x_3268_, v___x_3276_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; size_t v_sz_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v_sz_3279_ = lean_array_size(v_alts_3252_);
v___x_3280_ = ((size_t)0ULL);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3270_, v_sz_3279_, v___x_3280_, v_alts_3252_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3296_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3284_ = v___x_3281_;
v_isShared_3285_ = v_isSharedCheck_3296_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3281_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3296_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_fvarId_3286_; lean_object* v___x_3288_; 
v_fvarId_3286_ = lean_ctor_get(v_a_3278_, 0);
lean_inc(v_fvarId_3286_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 3, v_a_3282_);
lean_ctor_set(v___x_3254_, 2, v_fvarId_3286_);
lean_ctor_set(v___x_3254_, 1, v_a_3258_);
lean_ctor_set(v___x_3254_, 0, v___x_3267_);
v___x_3288_ = v___x_3254_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_a_3258_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_fvarId_3286_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v_a_3282_);
v___x_3288_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3289_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_a_3278_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v_a_3264_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3291_);
v___x_3293_ = v___x_3284_;
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
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3278_);
lean_dec(v_a_3264_);
lean_dec(v_a_3258_);
lean_del_object(v___x_3254_);
v_a_3297_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3281_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3281_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref_known(v___x_3270_, 1);
lean_dec(v_a_3264_);
lean_dec(v_a_3258_);
lean_del_object(v___x_3254_);
lean_dec_ref(v_alts_3252_);
v_a_3305_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3277_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3277_);
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
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec(v_a_3258_);
lean_del_object(v___x_3254_);
lean_dec_ref(v_alts_3252_);
lean_dec(v_discr_3251_);
v_a_3313_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3263_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3263_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_del_object(v___x_3254_);
lean_dec_ref(v_alts_3252_);
lean_dec(v_discr_3251_);
v_a_3321_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3257_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3257_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesNatToMono___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3243_ = stack[0].m_obj;
lean_object* v_a_3244_ = stack[1].m_obj;
lean_object* v_a_3245_ = stack[2].m_obj;
lean_object* v_a_3246_ = stack[3].m_obj;
lean_object* v_a_3247_ = stack[4].m_obj;
lean_object* v_a_3248_ = stack[5].m_obj;
lean_object* v_res_3331_;
v_res_3331_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_);
stack->m_obj
 = v_res_3331_;
}
lean_object* l_Lean_Compiler_LCNF_Code_toMono(lean_object* v_code_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_decl_3340_; lean_object* v_k_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; 
switch(lean_obj_tag(v_code_3332_))
{
case 0:
{
lean_object* v_decl_3456_; lean_object* v_k_3457_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v_value_3513_; 
v_decl_3456_ = lean_ctor_get(v_code_3332_, 0);
v_k_3457_ = lean_ctor_get(v_code_3332_, 1);
v_value_3513_ = lean_ctor_get(v_decl_3456_, 3);
lean_inc(v_value_3513_);
if (lean_obj_tag(v_value_3513_) == 3)
{
lean_object* v_declName_3514_; 
v_declName_3514_ = lean_ctor_get(v_value_3513_, 0);
lean_inc(v_declName_3514_);
if (lean_obj_tag(v_declName_3514_) == 1)
{
lean_object* v_pre_3515_; 
v_pre_3515_ = lean_ctor_get(v_declName_3514_, 0);
lean_inc(v_pre_3515_);
if (lean_obj_tag(v_pre_3515_) == 1)
{
lean_object* v_pre_3516_; 
v_pre_3516_ = lean_ctor_get(v_pre_3515_, 0);
if (lean_obj_tag(v_pre_3516_) == 0)
{
lean_object* v_type_3517_; lean_object* v_args_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3588_; 
v_type_3517_ = lean_ctor_get(v_decl_3456_, 2);
v_args_3518_ = lean_ctor_get(v_value_3513_, 2);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_value_3513_);
if (v_isSharedCheck_3588_ == 0)
{
lean_object* v_unused_3589_; lean_object* v_unused_3590_; 
v_unused_3589_ = lean_ctor_get(v_value_3513_, 1);
lean_dec(v_unused_3589_);
v_unused_3590_ = lean_ctor_get(v_value_3513_, 0);
lean_dec(v_unused_3590_);
v___x_3520_ = v_value_3513_;
v_isShared_3521_ = v_isSharedCheck_3588_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_args_3518_);
lean_dec(v_value_3513_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3588_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v_str_3522_; lean_object* v_str_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_str_3522_ = lean_ctor_get(v_declName_3514_, 1);
lean_inc_ref(v_str_3522_);
lean_dec_ref_known(v_declName_3514_, 2);
v_str_3523_ = lean_ctor_get(v_pre_3515_, 1);
lean_inc_ref(v_str_3523_);
lean_dec_ref_known(v_pre_3515_, 2);
v___x_3524_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__5));
v___x_3525_ = lean_string_dec_eq(v_str_3523_, v___x_3524_);
lean_dec_ref(v_str_3523_);
if (v___x_3525_ == 0)
{
lean_dec_ref(v_str_3522_);
lean_del_object(v___x_3520_);
lean_dec_ref(v_args_3518_);
v___y_3459_ = v_a_3333_;
v___y_3460_ = v_a_3334_;
v___y_3461_ = v_a_3335_;
v___y_3462_ = v_a_3336_;
v___y_3463_ = v_a_3337_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3526_ = ((lean_object*)(l_Lean_Compiler_LCNF_LetValue_toMono___closed__8));
v___x_3527_ = lean_string_dec_eq(v_str_3522_, v___x_3526_);
lean_dec_ref(v_str_3522_);
if (v___x_3527_ == 0)
{
lean_del_object(v___x_3520_);
lean_dec_ref(v_args_3518_);
v___y_3459_ = v_a_3333_;
v___y_3460_ = v_a_3334_;
v___y_3461_ = v_a_3335_;
v___y_3462_ = v_a_3336_;
v___y_3463_ = v_a_3337_;
goto v___jp_3458_;
}
else
{
lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3585_; 
lean_inc_ref(v_type_3517_);
lean_inc_ref(v_k_3457_);
lean_inc_ref(v_decl_3456_);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; lean_object* v_unused_3587_; 
v_unused_3586_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3586_);
v_unused_3587_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3587_);
v___x_3529_ = v_code_3332_;
v_isShared_3530_ = v_isSharedCheck_3585_;
goto v_resetjp_3528_;
}
else
{
lean_dec(v_code_3332_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3585_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3531_ = lean_array_get_size(v_args_3518_);
v___x_3532_ = lean_unsigned_to_nat(1u);
v___x_3533_ = lean_nat_dec_eq(v___x_3531_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_del_object(v___x_3529_);
lean_del_object(v___x_3520_);
lean_dec_ref(v_args_3518_);
lean_dec_ref(v_type_3517_);
lean_dec_ref(v_k_3457_);
lean_dec_ref(v_decl_3456_);
v___x_3534_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__5, &l_Lean_Compiler_LCNF_Code_toMono___closed__5_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__5);
v___x_3535_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3534_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3535_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_array_fget(v_args_3518_, v___x_3536_);
lean_dec_ref(v_args_3518_);
v___x_3538_ = 0;
v___x_3539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___closed__6));
v___x_3540_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesThunkToMono___redArg___closed__5));
v___x_3541_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(v___x_3538_, v___x_3539_, v___x_3540_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v_fvarId_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v_fvarId_3543_ = lean_ctor_get(v_a_3542_, 0);
v___x_3544_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__7));
v___x_3545_ = lean_box(0);
lean_inc(v_fvarId_3543_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_fvarId_3543_);
v___x_3547_ = lean_unsigned_to_nat(2u);
v___x_3548_ = lean_mk_empty_array_with_capacity(v___x_3547_);
v___x_3549_ = lean_array_push(v___x_3548_, v___x_3537_);
v___x_3550_ = lean_array_push(v___x_3549_, v___x_3546_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 2, v___x_3550_);
lean_ctor_set(v___x_3520_, 1, v___x_3545_);
lean_ctor_set(v___x_3520_, 0, v___x_3544_);
v___x_3552_ = v___x_3520_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; 
v___x_3553_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(v___x_3538_, v_decl_3456_, v_type_3517_, v___x_3552_, v_a_3335_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v_a_3554_; lean_object* v___x_3555_; 
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_a_3554_);
lean_dec_ref_known(v___x_3553_, 1);
v___x_3555_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3457_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3567_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3567_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3567_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 1, v_a_3556_);
lean_ctor_set(v___x_3529_, 0, v_a_3554_);
v___x_3561_ = v___x_3529_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3554_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3562_, 0, v_a_3542_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3562_);
v___x_3564_ = v___x_3558_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3562_);
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
else
{
lean_dec(v_a_3554_);
lean_dec(v_a_3542_);
lean_del_object(v___x_3529_);
return v___x_3555_;
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec(v_a_3542_);
lean_del_object(v___x_3529_);
lean_dec_ref(v_k_3457_);
v_a_3568_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3553_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3553_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v___x_3537_);
lean_del_object(v___x_3529_);
lean_del_object(v___x_3520_);
lean_dec_ref(v_type_3517_);
lean_dec_ref(v_k_3457_);
lean_dec_ref(v_decl_3456_);
v_a_3577_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3541_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3541_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
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
lean_dec_ref_known(v_pre_3515_, 2);
lean_dec_ref_known(v_declName_3514_, 2);
lean_dec_ref_known(v_value_3513_, 3);
v___y_3459_ = v_a_3333_;
v___y_3460_ = v_a_3334_;
v___y_3461_ = v_a_3335_;
v___y_3462_ = v_a_3336_;
v___y_3463_ = v_a_3337_;
goto v___jp_3458_;
}
}
else
{
lean_dec_ref_known(v_declName_3514_, 2);
lean_dec(v_pre_3515_);
lean_dec_ref_known(v_value_3513_, 3);
v___y_3459_ = v_a_3333_;
v___y_3460_ = v_a_3334_;
v___y_3461_ = v_a_3335_;
v___y_3462_ = v_a_3336_;
v___y_3463_ = v_a_3337_;
goto v___jp_3458_;
}
}
else
{
lean_dec(v_declName_3514_);
lean_dec_ref_known(v_value_3513_, 3);
v___y_3459_ = v_a_3333_;
v___y_3460_ = v_a_3334_;
v___y_3461_ = v_a_3335_;
v___y_3462_ = v_a_3336_;
v___y_3463_ = v_a_3337_;
goto v___jp_3458_;
}
}
else
{
lean_dec(v_value_3513_);
v___y_3459_ = v_a_3333_;
v___y_3460_ = v_a_3334_;
v___y_3461_ = v_a_3335_;
v___y_3462_ = v_a_3336_;
v___y_3463_ = v_a_3337_;
goto v___jp_3458_;
}
v___jp_3458_:
{
lean_object* v___x_3464_; 
lean_inc_ref(v_decl_3456_);
v___x_3464_ = l_Lean_Compiler_LCNF_LetDecl_toMono(v_decl_3456_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
lean_inc_ref(v_k_3457_);
v___x_3466_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3457_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3504_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3504_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3504_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
size_t v___x_3471_; size_t v___x_3472_; uint8_t v___x_3473_; 
v___x_3471_ = lean_ptr_addr(v_k_3457_);
v___x_3472_ = lean_ptr_addr(v_a_3467_);
v___x_3473_ = lean_usize_dec_eq(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3483_; 
v_isSharedCheck_3483_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; lean_object* v_unused_3485_; 
v_unused_3484_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3484_);
v_unused_3485_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3485_);
v___x_3475_ = v_code_3332_;
v_isShared_3476_ = v_isSharedCheck_3483_;
goto v_resetjp_3474_;
}
else
{
lean_dec(v_code_3332_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3483_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v_a_3467_);
lean_ctor_set(v___x_3475_, 0, v_a_3465_);
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3465_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_a_3467_);
v___x_3478_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3478_);
v___x_3480_ = v___x_3469_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
size_t v___x_3486_; size_t v___x_3487_; uint8_t v___x_3488_; 
v___x_3486_ = lean_ptr_addr(v_decl_3456_);
v___x_3487_ = lean_ptr_addr(v_a_3465_);
v___x_3488_ = lean_usize_dec_eq(v___x_3486_, v___x_3487_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3498_; 
v_isSharedCheck_3498_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; lean_object* v_unused_3500_; 
v_unused_3499_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3500_);
v___x_3490_ = v_code_3332_;
v_isShared_3491_ = v_isSharedCheck_3498_;
goto v_resetjp_3489_;
}
else
{
lean_dec(v_code_3332_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3498_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v_a_3467_);
lean_ctor_set(v___x_3490_, 0, v_a_3465_);
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3465_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_a_3467_);
v___x_3493_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3495_; 
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3493_);
v___x_3495_ = v___x_3469_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v___x_3502_; 
lean_dec(v_a_3467_);
lean_dec(v_a_3465_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v_code_3332_);
v___x_3502_ = v___x_3469_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_code_3332_);
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
}
else
{
lean_dec(v_a_3465_);
lean_dec_ref_known(v_code_3332_, 2);
return v___x_3466_;
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref_known(v_code_3332_, 2);
v_a_3505_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3464_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3464_);
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
case 3:
{
lean_object* v_fvarId_3591_; lean_object* v_args_3592_; size_t v_sz_3593_; size_t v___x_3594_; lean_object* v___x_3595_; 
v_fvarId_3591_ = lean_ctor_get(v_code_3332_, 0);
v_args_3592_ = lean_ctor_get(v_code_3332_, 1);
v_sz_3593_ = lean_array_size(v_args_3592_);
v___x_3594_ = ((size_t)0ULL);
lean_inc_ref(v_args_3592_);
v___x_3595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_ctorAppToMono_spec__1___redArg(v_sz_3593_, v___x_3594_, v_args_3592_, v_a_3333_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3621_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3621_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3621_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
uint8_t v___y_3601_; uint8_t v___x_3617_; 
v___x_3617_ = l_Lean_instBEqFVarId_beq(v_fvarId_3591_, v_fvarId_3591_);
if (v___x_3617_ == 0)
{
v___y_3601_ = v___x_3617_;
goto v___jp_3600_;
}
else
{
size_t v___x_3618_; size_t v___x_3619_; uint8_t v___x_3620_; 
v___x_3618_ = lean_ptr_addr(v_args_3592_);
v___x_3619_ = lean_ptr_addr(v_a_3596_);
v___x_3620_ = lean_usize_dec_eq(v___x_3618_, v___x_3619_);
v___y_3601_ = v___x_3620_;
goto v___jp_3600_;
}
v___jp_3600_:
{
if (v___y_3601_ == 0)
{
lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3611_; 
lean_inc(v_fvarId_3591_);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; lean_object* v_unused_3613_; 
v_unused_3612_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3612_);
v_unused_3613_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3613_);
v___x_3603_ = v_code_3332_;
v_isShared_3604_ = v_isSharedCheck_3611_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v_code_3332_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3611_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 1, v_a_3596_);
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_fvarId_3591_);
lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_a_3596_);
v___x_3606_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3608_; 
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3606_);
v___x_3608_ = v___x_3598_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
else
{
lean_object* v___x_3615_; 
lean_dec(v_a_3596_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v_code_3332_);
v___x_3615_ = v___x_3598_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_code_3332_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref_known(v_code_3332_, 2);
v_a_3622_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3595_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3595_);
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
case 4:
{
lean_object* v_cases_3630_; lean_object* v_typeName_3631_; lean_object* v_resultType_3632_; lean_object* v_discr_3633_; lean_object* v_alts_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v_cases_3630_ = lean_ctor_get(v_code_3332_, 0);
lean_inc_ref(v_cases_3630_);
v_typeName_3631_ = lean_ctor_get(v_cases_3630_, 0);
v_resultType_3632_ = lean_ctor_get(v_cases_3630_, 1);
v_discr_3633_ = lean_ctor_get(v_cases_3630_, 2);
v_alts_3634_ = lean_ctor_get(v_cases_3630_, 3);
v___x_3635_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesNatToMono___redArg___closed__0));
v___x_3636_ = lean_name_eq(v_typeName_3631_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = ((lean_object*)(l_Lean_Compiler_LCNF_casesIntToMono___redArg___closed__3));
v___x_3638_ = lean_name_eq(v_typeName_3631_, v___x_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__9));
v___x_3640_ = lean_name_eq(v_typeName_3631_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__11));
v___x_3642_ = lean_name_eq(v_typeName_3631_, v___x_3641_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3643_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__13));
v___x_3644_ = lean_name_eq(v_typeName_3631_, v___x_3643_);
if (v___x_3644_ == 0)
{
lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3645_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__15));
v___x_3646_ = lean_name_eq(v_typeName_3631_, v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3647_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__16));
v___x_3648_ = lean_name_eq(v_typeName_3631_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3649_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__17));
v___x_3650_ = lean_name_eq(v_typeName_3631_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3651_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__18));
v___x_3652_ = lean_name_eq(v_typeName_3631_, v___x_3651_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; uint8_t v___x_3654_; 
v___x_3653_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__19));
v___x_3654_ = lean_name_eq(v_typeName_3631_, v___x_3653_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; uint8_t v___x_3656_; 
v___x_3655_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__20));
v___x_3656_ = lean_name_eq(v_typeName_3631_, v___x_3655_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___x_3657_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__21));
v___x_3658_ = lean_name_eq(v_typeName_3631_, v___x_3657_);
if (v___x_3658_ == 0)
{
lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__22));
v___x_3660_ = lean_name_eq(v_typeName_3631_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
v___x_3661_ = ((lean_object*)(l_Lean_Compiler_LCNF_Code_toMono___closed__23));
v___x_3662_ = lean_name_eq(v_typeName_3631_, v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; 
lean_inc(v_typeName_3631_);
v___x_3663_ = l_Lean_Compiler_LCNF_hasTrivialStructure_x3f(v_typeName_3631_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
if (lean_obj_tag(v_a_3664_) == 1)
{
lean_object* v_val_3665_; lean_object* v___x_3666_; 
lean_dec_ref_known(v_code_3332_, 1);
v_val_3665_ = lean_ctor_get(v_a_3664_, 0);
lean_inc(v_val_3665_);
lean_dec_ref_known(v_a_3664_, 1);
v___x_3666_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_val_3665_, v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
lean_dec(v_val_3665_);
return v___x_3666_;
}
else
{
lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3757_; 
lean_inc_ref(v_alts_3634_);
lean_inc(v_discr_3633_);
lean_inc_ref(v_resultType_3632_);
lean_inc(v_typeName_3631_);
lean_dec(v_a_3664_);
v_isSharedCheck_3757_ = !lean_is_exclusive(v_cases_3630_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3758_ = lean_ctor_get(v_cases_3630_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_cases_3630_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_cases_3630_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_cases_3630_, 0);
lean_dec(v_unused_3761_);
v___x_3668_ = v_cases_3630_;
v_isShared_3669_ = v_isSharedCheck_3757_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v_cases_3630_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3757_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; 
lean_inc_ref(v_resultType_3632_);
v___x_3670_ = l_Lean_Compiler_LCNF_toMonoType(v_resultType_3632_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3748_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3748_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3748_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v_env_3676_; lean_object* v___x_3703_; 
v___x_3675_ = lean_st_ref_get(v_a_3337_);
v_env_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc_ref_n(v_env_3676_, 2);
lean_dec(v___x_3675_);
lean_inc(v_typeName_3631_);
v___x_3703_ = l_Lean_Environment_find_x3f(v_env_3676_, v_typeName_3631_, v___x_3662_);
if (lean_obj_tag(v___x_3703_) == 1)
{
lean_object* v_val_3704_; 
v_val_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_val_3704_);
lean_dec_ref_known(v___x_3703_, 1);
if (lean_obj_tag(v_val_3704_) == 5)
{
lean_object* v_val_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3747_; 
v_val_3705_ = lean_ctor_get(v_val_3704_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_val_3704_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3707_ = v_val_3704_;
v_isShared_3708_ = v_isSharedCheck_3747_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_val_3705_);
lean_dec(v_val_3704_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3747_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v_toConstantVal_3709_; lean_object* v_name_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_toConstantVal_3709_ = lean_ctor_get(v_val_3705_, 0);
lean_inc_ref(v_toConstantVal_3709_);
lean_dec_ref(v_val_3705_);
v_name_3710_ = lean_ctor_get(v_toConstantVal_3709_, 0);
lean_inc(v_name_3710_);
lean_dec_ref(v_toConstantVal_3709_);
v___x_3711_ = l_Lean_mkCasesOnName(v_name_3710_);
lean_inc_ref(v_env_3676_);
v___x_3712_ = l_Lean_Compiler_getImplementedBy_x3f(v_env_3676_, v___x_3711_);
if (lean_obj_tag(v___x_3712_) == 0)
{
if (v___x_3662_ == 0)
{
size_t v_sz_3713_; size_t v___x_3714_; lean_object* v___x_3715_; 
lean_dec_ref(v_env_3676_);
lean_del_object(v___x_3668_);
v_sz_3713_ = lean_array_size(v_alts_3634_);
v___x_3714_ = ((size_t)0ULL);
lean_inc_ref(v_alts_3634_);
v___x_3715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_3713_, v___x_3714_, v_alts_3634_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3738_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3718_ = v___x_3715_;
v_isShared_3719_ = v_isSharedCheck_3738_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3715_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3738_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
size_t v___x_3728_; size_t v___x_3729_; uint8_t v___x_3730_; 
v___x_3728_ = lean_ptr_addr(v_alts_3634_);
lean_dec_ref(v_alts_3634_);
v___x_3729_ = lean_ptr_addr(v_a_3716_);
v___x_3730_ = lean_usize_dec_eq(v___x_3728_, v___x_3729_);
if (v___x_3730_ == 0)
{
lean_del_object(v___x_3673_);
lean_dec_ref(v_resultType_3632_);
lean_dec_ref_known(v_code_3332_, 1);
goto v___jp_3720_;
}
else
{
size_t v___x_3731_; size_t v___x_3732_; uint8_t v___x_3733_; 
v___x_3731_ = lean_ptr_addr(v_resultType_3632_);
lean_dec_ref(v_resultType_3632_);
v___x_3732_ = lean_ptr_addr(v_a_3671_);
v___x_3733_ = lean_usize_dec_eq(v___x_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_del_object(v___x_3673_);
lean_dec_ref_known(v_code_3332_, 1);
goto v___jp_3720_;
}
else
{
uint8_t v___x_3734_; 
v___x_3734_ = l_Lean_instBEqFVarId_beq(v_discr_3633_, v_discr_3633_);
if (v___x_3734_ == 0)
{
lean_del_object(v___x_3673_);
lean_dec_ref_known(v_code_3332_, 1);
goto v___jp_3720_;
}
else
{
lean_object* v___x_3736_; 
lean_del_object(v___x_3718_);
lean_dec(v_a_3716_);
lean_del_object(v___x_3707_);
lean_dec(v_a_3671_);
lean_dec(v_discr_3633_);
lean_dec(v_typeName_3631_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_code_3332_);
v___x_3736_ = v___x_3673_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_code_3332_);
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
v___jp_3720_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3721_, 0, v_typeName_3631_);
lean_ctor_set(v___x_3721_, 1, v_a_3671_);
lean_ctor_set(v___x_3721_, 2, v_discr_3633_);
lean_ctor_set(v___x_3721_, 3, v_a_3716_);
if (v_isShared_3708_ == 0)
{
lean_ctor_set_tag(v___x_3707_, 4);
lean_ctor_set(v___x_3707_, 0, v___x_3721_);
v___x_3723_ = v___x_3707_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3719_ == 0)
{
lean_ctor_set(v___x_3718_, 0, v___x_3723_);
v___x_3725_ = v___x_3718_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_del_object(v___x_3707_);
lean_del_object(v___x_3673_);
lean_dec(v_a_3671_);
lean_dec_ref(v_alts_3634_);
lean_dec(v_discr_3633_);
lean_dec_ref(v_resultType_3632_);
lean_dec(v_typeName_3631_);
lean_dec_ref_known(v_code_3332_, 1);
v_a_3739_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3715_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3715_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_del_object(v___x_3707_);
lean_del_object(v___x_3673_);
lean_dec_ref(v_resultType_3632_);
lean_dec_ref_known(v_code_3332_, 1);
goto v___jp_3677_;
}
}
else
{
lean_dec_ref_known(v___x_3712_, 1);
lean_del_object(v___x_3707_);
lean_del_object(v___x_3673_);
lean_dec_ref(v_resultType_3632_);
lean_dec_ref_known(v_code_3332_, 1);
goto v___jp_3677_;
}
}
}
else
{
lean_dec(v_val_3704_);
lean_dec_ref(v_env_3676_);
lean_del_object(v___x_3673_);
lean_dec(v_a_3671_);
lean_del_object(v___x_3668_);
lean_dec_ref(v_alts_3634_);
lean_dec(v_discr_3633_);
lean_dec_ref(v_resultType_3632_);
lean_dec(v_typeName_3631_);
lean_dec_ref_known(v_code_3332_, 1);
v___y_3449_ = v_a_3333_;
v___y_3450_ = v_a_3334_;
v___y_3451_ = v_a_3335_;
v___y_3452_ = v_a_3336_;
v___y_3453_ = v_a_3337_;
goto v___jp_3448_;
}
}
else
{
lean_dec(v___x_3703_);
lean_dec_ref(v_env_3676_);
lean_del_object(v___x_3673_);
lean_dec(v_a_3671_);
lean_del_object(v___x_3668_);
lean_dec_ref(v_alts_3634_);
lean_dec(v_discr_3633_);
lean_dec_ref(v_resultType_3632_);
lean_dec(v_typeName_3631_);
lean_dec_ref_known(v_code_3332_, 1);
v___y_3449_ = v_a_3333_;
v___y_3450_ = v_a_3334_;
v___y_3451_ = v_a_3335_;
v___y_3452_ = v_a_3336_;
v___y_3453_ = v_a_3337_;
goto v___jp_3448_;
}
v___jp_3677_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; size_t v_sz_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v___x_3678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___closed__4));
v___x_3679_ = l_Lean_Name_append(v_typeName_3631_, v___x_3678_);
v_sz_3680_ = lean_array_size(v_alts_3634_);
v___x_3681_ = ((size_t)0ULL);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v_env_3676_, v___x_3662_, v_sz_3680_, v___x_3681_, v_alts_3634_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3694_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3694_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3694_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 3, v_a_3683_);
lean_ctor_set(v___x_3668_, 1, v_a_3671_);
lean_ctor_set(v___x_3668_, 0, v___x_3679_);
v___x_3688_ = v___x_3668_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_a_3671_);
lean_ctor_set(v_reuseFailAlloc_3693_, 2, v_discr_3633_);
lean_ctor_set(v_reuseFailAlloc_3693_, 3, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3689_);
v___x_3691_ = v___x_3685_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
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
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v___x_3679_);
lean_dec(v_a_3671_);
lean_del_object(v___x_3668_);
lean_dec(v_discr_3633_);
v_a_3695_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3682_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3682_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_del_object(v___x_3668_);
lean_dec_ref(v_alts_3634_);
lean_dec(v_discr_3633_);
lean_dec_ref(v_resultType_3632_);
lean_dec(v_typeName_3631_);
lean_dec_ref_known(v_code_3332_, 1);
v_a_3749_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3670_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3670_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec_ref(v_cases_3630_);
lean_dec_ref_known(v_code_3332_, 1);
v_a_3762_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3663_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3663_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v___x_3770_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3770_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3770_;
}
}
else
{
lean_object* v___x_3771_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3771_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
lean_dec_ref(v_cases_3630_);
return v___x_3771_;
}
}
else
{
lean_object* v___x_3772_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3772_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3772_;
}
}
else
{
lean_object* v___x_3773_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3773_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3773_;
}
}
else
{
lean_object* v___x_3774_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3774_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3774_;
}
}
else
{
lean_object* v___x_3775_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3775_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3775_;
}
}
else
{
lean_object* v___x_3776_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3776_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3776_;
}
}
else
{
lean_object* v___x_3777_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3777_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3777_;
}
}
else
{
lean_object* v___x_3778_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3778_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3630_, v___x_3645_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3778_;
}
}
else
{
lean_object* v___x_3779_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3779_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3630_, v___x_3643_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3779_;
}
}
else
{
lean_object* v___x_3780_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3780_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3630_, v___x_3641_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3780_;
}
}
else
{
lean_object* v___x_3781_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3781_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_cases_3630_, v___x_3639_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3781_;
}
}
else
{
lean_object* v___x_3782_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3782_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3782_;
}
}
else
{
lean_object* v___x_3783_; 
lean_dec_ref_known(v_code_3332_, 1);
v___x_3783_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_cases_3630_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3783_;
}
}
case 5:
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_code_3332_);
return v___x_3784_;
}
case 6:
{
lean_object* v_type_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3809_; 
v_type_3785_ = lean_ctor_get(v_code_3332_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3787_ = v_code_3332_;
v_isShared_3788_ = v_isSharedCheck_3809_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_type_3785_);
lean_dec(v_code_3332_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3809_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3785_, v_a_3336_, v_a_3337_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3800_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3792_ = v___x_3789_;
v_isShared_3793_ = v_isSharedCheck_3800_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3789_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3800_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v_a_3790_);
v___x_3795_ = v___x_3787_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
lean_object* v___x_3797_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3795_);
v___x_3797_ = v___x_3792_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
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
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_del_object(v___x_3787_);
v_a_3801_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3789_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3789_);
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
default: 
{
lean_object* v_decl_3810_; lean_object* v_k_3811_; 
v_decl_3810_ = lean_ctor_get(v_code_3332_, 0);
v_k_3811_ = lean_ctor_get(v_code_3332_, 1);
lean_inc_ref(v_k_3811_);
lean_inc_ref(v_decl_3810_);
v_decl_3340_ = v_decl_3810_;
v_k_3341_ = v_k_3811_;
v___y_3342_ = v_a_3333_;
v___y_3343_ = v_a_3334_;
v___y_3344_ = v_a_3335_;
v___y_3345_ = v_a_3336_;
v___y_3346_ = v_a_3337_;
goto v___jp_3339_;
}
}
v___jp_3339_:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3340_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = l_Lean_Compiler_LCNF_Code_toMono(v_k_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3349_) == 0)
{
switch(lean_obj_tag(v_code_3332_))
{
case 1:
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3389_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3389_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3389_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_decl_3354_; lean_object* v_k_3355_; size_t v___x_3356_; size_t v___x_3357_; uint8_t v___x_3358_; 
v_decl_3354_ = lean_ctor_get(v_code_3332_, 0);
v_k_3355_ = lean_ctor_get(v_code_3332_, 1);
v___x_3356_ = lean_ptr_addr(v_k_3355_);
v___x_3357_ = lean_ptr_addr(v_a_3350_);
v___x_3358_ = lean_usize_dec_eq(v___x_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; lean_object* v_unused_3370_; 
v_unused_3369_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3369_);
v_unused_3370_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3370_);
v___x_3360_ = v_code_3332_;
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
else
{
lean_dec(v_code_3332_);
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
lean_ctor_set(v___x_3360_, 0, v_a_3348_);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3348_);
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
v___x_3372_ = lean_ptr_addr(v_a_3348_);
v___x_3373_ = lean_usize_dec_eq(v___x_3371_, v___x_3372_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3383_; 
v_isSharedCheck_3383_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3383_ == 0)
{
lean_object* v_unused_3384_; lean_object* v_unused_3385_; 
v_unused_3384_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3384_);
v_unused_3385_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3385_);
v___x_3375_ = v_code_3332_;
v_isShared_3376_ = v_isSharedCheck_3383_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_code_3332_);
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
lean_ctor_set(v___x_3375_, 0, v_a_3348_);
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3348_);
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
lean_dec(v_a_3348_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v_code_3332_);
v___x_3387_ = v___x_3352_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_code_3332_);
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
case 2:
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3429_; 
v_a_3390_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3392_ = v___x_3349_;
v_isShared_3393_ = v_isSharedCheck_3429_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3349_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3429_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_decl_3394_; lean_object* v_k_3395_; size_t v___x_3396_; size_t v___x_3397_; uint8_t v___x_3398_; 
v_decl_3394_ = lean_ctor_get(v_code_3332_, 0);
v_k_3395_ = lean_ctor_get(v_code_3332_, 1);
v___x_3396_ = lean_ptr_addr(v_k_3395_);
v___x_3397_ = lean_ptr_addr(v_a_3390_);
v___x_3398_ = lean_usize_dec_eq(v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3408_; 
v_isSharedCheck_3408_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; lean_object* v_unused_3410_; 
v_unused_3409_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3410_);
v___x_3400_ = v_code_3332_;
v_isShared_3401_ = v_isSharedCheck_3408_;
goto v_resetjp_3399_;
}
else
{
lean_dec(v_code_3332_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3408_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 1, v_a_3390_);
lean_ctor_set(v___x_3400_, 0, v_a_3348_);
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3348_);
lean_ctor_set(v_reuseFailAlloc_3407_, 1, v_a_3390_);
v___x_3403_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3405_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3403_);
v___x_3405_ = v___x_3392_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
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
else
{
size_t v___x_3411_; size_t v___x_3412_; uint8_t v___x_3413_; 
v___x_3411_ = lean_ptr_addr(v_decl_3394_);
v___x_3412_ = lean_ptr_addr(v_a_3348_);
v___x_3413_ = lean_usize_dec_eq(v___x_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3423_; 
v_isSharedCheck_3423_ = !lean_is_exclusive(v_code_3332_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; lean_object* v_unused_3425_; 
v_unused_3424_ = lean_ctor_get(v_code_3332_, 1);
lean_dec(v_unused_3424_);
v_unused_3425_ = lean_ctor_get(v_code_3332_, 0);
lean_dec(v_unused_3425_);
v___x_3415_ = v_code_3332_;
v_isShared_3416_ = v_isSharedCheck_3423_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v_code_3332_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3423_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 1, v_a_3390_);
lean_ctor_set(v___x_3415_, 0, v_a_3348_);
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3348_);
lean_ctor_set(v_reuseFailAlloc_3422_, 1, v_a_3390_);
v___x_3418_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v___x_3418_);
v___x_3420_ = v___x_3392_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v___x_3427_; 
lean_dec(v_a_3390_);
lean_dec(v_a_3348_);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 0, v_code_3332_);
v___x_3427_ = v___x_3392_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_code_3332_);
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
}
default: 
{
lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3438_; 
lean_dec(v_a_3348_);
lean_dec_ref(v_code_3332_);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v___x_3349_, 0);
lean_dec(v_unused_3439_);
v___x_3431_ = v___x_3349_;
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v___x_3349_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3438_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3436_; 
v___x_3433_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__2, &l_Lean_Compiler_LCNF_Code_toMono___closed__2_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__2);
v___x_3434_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__2(v___x_3433_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3434_);
v___x_3436_ = v___x_3431_;
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
}
else
{
lean_dec(v_a_3348_);
lean_dec_ref(v_code_3332_);
return v___x_3349_;
}
}
else
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3447_; 
lean_dec_ref(v_k_3341_);
lean_dec_ref(v_code_3332_);
v_a_3440_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3442_ = v___x_3347_;
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3347_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3447_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
if (v_isShared_3443_ == 0)
{
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
}
v___jp_3448_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_obj_once(&l_Lean_Compiler_LCNF_Code_toMono___closed__4, &l_Lean_Compiler_LCNF_Code_toMono___closed__4_once, _init_l_Lean_Compiler_LCNF_Code_toMono___closed__4);
v___x_3455_ = l_panic___at___00Lean_Compiler_LCNF_Code_toMono_spec__3(v___x_3454_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
return v___x_3455_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_toMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_code_3332_ = stack[0].m_obj;
lean_object* v_a_3333_ = stack[1].m_obj;
lean_object* v_a_3334_ = stack[2].m_obj;
lean_object* v_a_3335_ = stack[3].m_obj;
lean_object* v_a_3336_ = stack[4].m_obj;
lean_object* v_a_3337_ = stack[5].m_obj;
lean_object* v_res_3812_;
v_res_3812_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
stack->m_obj
 = v_res_3812_;
}
lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono(lean_object* v_decl_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v_params_3820_; lean_object* v_type_3821_; lean_object* v_value_3822_; uint8_t v___x_3823_; lean_object* v___x_3824_; 
v_params_3820_ = lean_ctor_get(v_decl_3813_, 2);
v_type_3821_ = lean_ctor_get(v_decl_3813_, 3);
v_value_3822_ = lean_ctor_get(v_decl_3813_, 4);
v___x_3823_ = 0;
lean_inc_ref(v_type_3821_);
v___x_3824_ = l_Lean_Compiler_LCNF_toMonoType(v_type_3821_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; size_t v_sz_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v_sz_3826_ = lean_array_size(v_params_3820_);
v___x_3827_ = ((size_t)0ULL);
lean_inc_ref(v_params_3820_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_3826_, v___x_3827_, v_params_3820_, v_a_3814_, v_a_3816_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
lean_inc_ref(v_value_3822_);
v___x_3830_ = l_Lean_Compiler_LCNF_Code_toMono(v_value_3822_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3832_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref_known(v___x_3830_, 1);
v___x_3832_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3823_, v_decl_3813_, v_a_3825_, v_a_3829_, v_a_3831_, v_a_3816_);
return v___x_3832_;
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec(v_a_3829_);
lean_dec(v_a_3825_);
lean_dec_ref(v_decl_3813_);
v_a_3833_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3830_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3830_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec(v_a_3825_);
lean_dec_ref(v_decl_3813_);
v_a_3841_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3828_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3828_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_decl_3813_);
v_a_3849_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3824_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3824_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_toMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3813_ = stack[0].m_obj;
lean_object* v_a_3814_ = stack[1].m_obj;
lean_object* v_a_3815_ = stack[2].m_obj;
lean_object* v_a_3816_ = stack[3].m_obj;
lean_object* v_a_3817_ = stack[4].m_obj;
lean_object* v_a_3818_ = stack[5].m_obj;
lean_object* v_res_3857_;
v_res_3857_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_);
stack->m_obj
 = v_res_3857_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_toMono___boxed(lean_object* v_decl_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Compiler_LCNF_FunDecl_toMono(v_decl_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6___boxed(lean_object* v_sz_3866_, lean_object* v_i_3867_, lean_object* v_bs_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
size_t v_sz_boxed_3875_; size_t v_i_boxed_3876_; lean_object* v_res_3877_; 
v_sz_boxed_3875_ = lean_unbox_usize(v_sz_3866_);
lean_dec(v_sz_3866_);
v_i_boxed_3876_ = lean_unbox_usize(v_i_3867_);
lean_dec(v_i_3867_);
v_res_3877_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__6(v_sz_boxed_3875_, v_i_boxed_3876_, v_bs_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___redArg___boxed(lean_object* v_c_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___redArg___boxed(lean_object* v_c_3886_, lean_object* v_uintName_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_3886_, v_uintName_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg___boxed(lean_object* v_c_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_){
_start:
{
lean_object* v_res_3902_; 
v_res_3902_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
lean_dec(v_a_3900_);
lean_dec_ref(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec_ref(v_a_3897_);
lean_dec(v_a_3896_);
return v_res_3902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg___boxed(lean_object* v_c_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg___boxed(lean_object* v_c_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_3911_, v_a_3912_, v_a_3913_, v_a_3914_, v_a_3915_, v_a_3916_);
lean_dec(v_a_3916_);
lean_dec_ref(v_a_3915_);
lean_dec(v_a_3914_);
lean_dec_ref(v_a_3913_);
lean_dec(v_a_3912_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___redArg___boxed(lean_object* v_c_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___redArg___boxed(lean_object* v_c_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec_ref(v_a_3929_);
lean_dec(v_a_3928_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5___boxed(lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v_sz_3937_, lean_object* v_i_3938_, lean_object* v_bs_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
uint8_t v___x_33875__boxed_3946_; size_t v_sz_boxed_3947_; size_t v_i_boxed_3948_; lean_object* v_res_3949_; 
v___x_33875__boxed_3946_ = lean_unbox(v___x_3936_);
v_sz_boxed_3947_ = lean_unbox_usize(v_sz_3937_);
lean_dec(v_sz_3937_);
v_i_boxed_3948_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_res_3949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Code_toMono_spec__5(v___x_3935_, v___x_33875__boxed_3946_, v_sz_boxed_3947_, v_i_boxed_3948_, v_bs_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
return v_res_3949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___redArg___boxed(lean_object* v_c_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
lean_dec(v_a_3951_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___redArg___boxed(lean_object* v_c_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec_ref(v_a_3960_);
lean_dec(v_a_3959_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___redArg___boxed(lean_object* v_c_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
lean_dec(v_a_3971_);
lean_dec_ref(v_a_3970_);
lean_dec(v_a_3969_);
lean_dec_ref(v_a_3968_);
lean_dec(v_a_3967_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_trivialStructToMono___boxed(lean_object* v_info_3974_, lean_object* v_c_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_){
_start:
{
lean_object* v_res_3982_; 
v_res_3982_ = l_Lean_Compiler_LCNF_trivialStructToMono(v_info_3974_, v_c_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_info_3974_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20___boxed(lean_object* v___x_3983_, lean_object* v_sz_3984_, lean_object* v_i_3985_, lean_object* v_bs_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
size_t v_sz_boxed_3993_; size_t v_i_boxed_3994_; lean_object* v_res_3995_; 
v_sz_boxed_3993_ = lean_unbox_usize(v_sz_3984_);
lean_dec(v_sz_3984_);
v_i_boxed_3994_ = lean_unbox_usize(v_i_3985_);
lean_dec(v_i_3985_);
v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesNatToMono_spec__20(v___x_3983_, v_sz_boxed_3993_, v_i_boxed_3994_, v_bs_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___redArg___boxed(lean_object* v_c_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_c_3996_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18___boxed(lean_object* v___x_4004_, lean_object* v_sz_4005_, lean_object* v_i_4006_, lean_object* v_bs_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
size_t v_sz_boxed_4014_; size_t v_i_boxed_4015_; lean_object* v_res_4016_; 
v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4005_);
lean_dec(v_sz_4005_);
v_i_boxed_4015_ = lean_unbox_usize(v_i_4006_);
lean_dec(v_i_4006_);
v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_casesIntToMono_spec__18(v___x_4004_, v_sz_boxed_4014_, v_i_boxed_4015_, v_bs_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_toMono___boxed(lean_object* v_code_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_Compiler_LCNF_Code_toMono(v_code_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
lean_dec(v_a_4022_);
lean_dec_ref(v_a_4021_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
return v_res_4024_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesTaskToMono(lean_object* v_c_4025_, lean_object* v_x_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_Compiler_LCNF_casesTaskToMono___redArg(v_c_4025_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
return v___x_4033_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesTaskToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4025_ = stack[0].m_obj;
lean_object* v_a_4027_ = stack[2].m_obj;
lean_object* v_a_4028_ = stack[3].m_obj;
lean_object* v_a_4029_ = stack[4].m_obj;
lean_object* v_a_4030_ = stack[5].m_obj;
lean_object* v_a_4031_ = stack[6].m_obj;
lean_object* v_res_4034_;
v_res_4034_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4025_, lean_box(0), v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
stack->m_obj
 = v_res_4034_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesTaskToMono___boxed(lean_object* v_c_4035_, lean_object* v_x_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_Compiler_LCNF_casesTaskToMono(v_c_4035_, v_x_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_);
lean_dec(v_a_4041_);
lean_dec_ref(v_a_4040_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
lean_dec(v_a_4037_);
return v_res_4043_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesThunkToMono(lean_object* v_c_4044_, lean_object* v_x_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Lean_Compiler_LCNF_casesThunkToMono___redArg(v_c_4044_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_);
return v___x_4052_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesThunkToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4044_ = stack[0].m_obj;
lean_object* v_a_4046_ = stack[2].m_obj;
lean_object* v_a_4047_ = stack[3].m_obj;
lean_object* v_a_4048_ = stack[4].m_obj;
lean_object* v_a_4049_ = stack[5].m_obj;
lean_object* v_a_4050_ = stack[6].m_obj;
lean_object* v_res_4053_;
v_res_4053_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4044_, lean_box(0), v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_);
stack->m_obj
 = v_res_4053_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesThunkToMono___boxed(lean_object* v_c_4054_, lean_object* v_x_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_Compiler_LCNF_casesThunkToMono(v_c_4054_, v_x_4055_, v_a_4056_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_);
lean_dec(v_a_4060_);
lean_dec_ref(v_a_4059_);
lean_dec(v_a_4058_);
lean_dec_ref(v_a_4057_);
lean_dec(v_a_4056_);
lean_dec_ref(v_c_4054_);
return v_res_4062_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono(lean_object* v_c_4063_, lean_object* v_x_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l_Lean_Compiler_LCNF_casesFloat32ToMono___redArg(v_c_4063_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesFloat32ToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4063_ = stack[0].m_obj;
lean_object* v_a_4065_ = stack[2].m_obj;
lean_object* v_a_4066_ = stack[3].m_obj;
lean_object* v_a_4067_ = stack[4].m_obj;
lean_object* v_a_4068_ = stack[5].m_obj;
lean_object* v_a_4069_ = stack[6].m_obj;
lean_object* v_res_4072_;
v_res_4072_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4063_, lean_box(0), v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
stack->m_obj
 = v_res_4072_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloat32ToMono___boxed(lean_object* v_c_4073_, lean_object* v_x_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_Compiler_LCNF_casesFloat32ToMono(v_c_4073_, v_x_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
return v_res_4081_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesFloatToMono(lean_object* v_c_4082_, lean_object* v_x_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4090_; 
v___x_4090_ = l_Lean_Compiler_LCNF_casesFloatToMono___redArg(v_c_4082_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
return v___x_4090_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesFloatToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4082_ = stack[0].m_obj;
lean_object* v_a_4084_ = stack[2].m_obj;
lean_object* v_a_4085_ = stack[3].m_obj;
lean_object* v_a_4086_ = stack[4].m_obj;
lean_object* v_a_4087_ = stack[5].m_obj;
lean_object* v_a_4088_ = stack[6].m_obj;
lean_object* v_res_4091_;
v_res_4091_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4082_, lean_box(0), v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
stack->m_obj
 = v_res_4091_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatToMono___boxed(lean_object* v_c_4092_, lean_object* v_x_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v_res_4100_; 
v_res_4100_ = l_Lean_Compiler_LCNF_casesFloatToMono(v_c_4092_, v_x_4093_, v_a_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
lean_dec(v_a_4098_);
lean_dec_ref(v_a_4097_);
lean_dec(v_a_4096_);
lean_dec_ref(v_a_4095_);
lean_dec(v_a_4094_);
return v_res_4100_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesStringToMono(lean_object* v_c_4101_, lean_object* v_x_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_Compiler_LCNF_casesStringToMono___redArg(v_c_4101_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesStringToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4101_ = stack[0].m_obj;
lean_object* v_a_4103_ = stack[2].m_obj;
lean_object* v_a_4104_ = stack[3].m_obj;
lean_object* v_a_4105_ = stack[4].m_obj;
lean_object* v_a_4106_ = stack[5].m_obj;
lean_object* v_a_4107_ = stack[6].m_obj;
lean_object* v_res_4110_;
v_res_4110_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4101_, lean_box(0), v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
stack->m_obj
 = v_res_4110_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesStringToMono___boxed(lean_object* v_c_4111_, lean_object* v_x_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_Compiler_LCNF_casesStringToMono(v_c_4111_, v_x_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
lean_dec(v_a_4115_);
lean_dec_ref(v_a_4114_);
lean_dec(v_a_4113_);
return v_res_4119_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono(lean_object* v_c_4120_, lean_object* v_x_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono___redArg(v_c_4120_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
return v___x_4128_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesFloatArrayToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4120_ = stack[0].m_obj;
lean_object* v_a_4122_ = stack[2].m_obj;
lean_object* v_a_4123_ = stack[3].m_obj;
lean_object* v_a_4124_ = stack[4].m_obj;
lean_object* v_a_4125_ = stack[5].m_obj;
lean_object* v_a_4126_ = stack[6].m_obj;
lean_object* v_res_4129_;
v_res_4129_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4120_, lean_box(0), v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
stack->m_obj
 = v_res_4129_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesFloatArrayToMono___boxed(lean_object* v_c_4130_, lean_object* v_x_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Compiler_LCNF_casesFloatArrayToMono(v_c_4130_, v_x_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
return v_res_4138_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono(lean_object* v_c_4139_, lean_object* v_x_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4147_; 
v___x_4147_ = l_Lean_Compiler_LCNF_casesByteArrayToMono___redArg(v_c_4139_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
return v___x_4147_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesByteArrayToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4139_ = stack[0].m_obj;
lean_object* v_a_4141_ = stack[2].m_obj;
lean_object* v_a_4142_ = stack[3].m_obj;
lean_object* v_a_4143_ = stack[4].m_obj;
lean_object* v_a_4144_ = stack[5].m_obj;
lean_object* v_a_4145_ = stack[6].m_obj;
lean_object* v_res_4148_;
v_res_4148_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4139_, lean_box(0), v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
stack->m_obj
 = v_res_4148_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesByteArrayToMono___boxed(lean_object* v_c_4149_, lean_object* v_x_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Compiler_LCNF_casesByteArrayToMono(v_c_4149_, v_x_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
return v_res_4157_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesArrayToMono(lean_object* v_c_4158_, lean_object* v_x_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_){
_start:
{
lean_object* v___x_4166_; 
v___x_4166_ = l_Lean_Compiler_LCNF_casesArrayToMono___redArg(v_c_4158_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
return v___x_4166_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesArrayToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4158_ = stack[0].m_obj;
lean_object* v_a_4160_ = stack[2].m_obj;
lean_object* v_a_4161_ = stack[3].m_obj;
lean_object* v_a_4162_ = stack[4].m_obj;
lean_object* v_a_4163_ = stack[5].m_obj;
lean_object* v_a_4164_ = stack[6].m_obj;
lean_object* v_res_4167_;
v_res_4167_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4158_, lean_box(0), v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
stack->m_obj
 = v_res_4167_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesArrayToMono___boxed(lean_object* v_c_4168_, lean_object* v_x_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_Compiler_LCNF_casesArrayToMono(v_c_4168_, v_x_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
return v_res_4176_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesUIntToMono(lean_object* v_c_4177_, lean_object* v_uintName_4178_, lean_object* v_x_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_Compiler_LCNF_casesUIntToMono___redArg(v_c_4177_, v_uintName_4178_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesUIntToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4177_ = stack[0].m_obj;
lean_object* v_uintName_4178_ = stack[1].m_obj;
lean_object* v_a_4180_ = stack[3].m_obj;
lean_object* v_a_4181_ = stack[4].m_obj;
lean_object* v_a_4182_ = stack[5].m_obj;
lean_object* v_a_4183_ = stack[6].m_obj;
lean_object* v_a_4184_ = stack[7].m_obj;
lean_object* v_res_4187_;
v_res_4187_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4177_, v_uintName_4178_, lean_box(0), v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_);
stack->m_obj
 = v_res_4187_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesUIntToMono___boxed(lean_object* v_c_4188_, lean_object* v_uintName_4189_, lean_object* v_x_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_Compiler_LCNF_casesUIntToMono(v_c_4188_, v_uintName_4189_, v_x_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
lean_dec(v_a_4195_);
lean_dec_ref(v_a_4194_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
return v_res_4197_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesIntToMono(lean_object* v_c_4198_, lean_object* v_x_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_Compiler_LCNF_casesIntToMono___redArg(v_c_4198_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
return v___x_4206_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesIntToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4198_ = stack[0].m_obj;
lean_object* v_a_4200_ = stack[2].m_obj;
lean_object* v_a_4201_ = stack[3].m_obj;
lean_object* v_a_4202_ = stack[4].m_obj;
lean_object* v_a_4203_ = stack[5].m_obj;
lean_object* v_a_4204_ = stack[6].m_obj;
lean_object* v_res_4207_;
v_res_4207_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4198_, lean_box(0), v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
stack->m_obj
 = v_res_4207_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesIntToMono___boxed(lean_object* v_c_4208_, lean_object* v_x_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Compiler_LCNF_casesIntToMono(v_c_4208_, v_x_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
lean_dec(v_a_4214_);
lean_dec_ref(v_a_4213_);
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_a_4210_);
return v_res_4216_;
}
}
lean_object* l_Lean_Compiler_LCNF_casesNatToMono(lean_object* v_c_4217_, lean_object* v_x_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Compiler_LCNF_casesNatToMono___redArg(v_c_4217_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_casesNatToMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_4217_ = stack[0].m_obj;
lean_object* v_a_4219_ = stack[2].m_obj;
lean_object* v_a_4220_ = stack[3].m_obj;
lean_object* v_a_4221_ = stack[4].m_obj;
lean_object* v_a_4222_ = stack[5].m_obj;
lean_object* v_a_4223_ = stack[6].m_obj;
lean_object* v_res_4226_;
v_res_4226_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4217_, lean_box(0), v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_);
stack->m_obj
 = v_res_4226_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_casesNatToMono___boxed(lean_object* v_c_4227_, lean_object* v_x_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_Compiler_LCNF_casesNatToMono(v_c_4227_, v_x_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
lean_dec(v_a_4231_);
lean_dec_ref(v_a_4230_);
lean_dec(v_a_4229_);
return v_res_4235_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(size_t v_sz_4236_, size_t v_i_4237_, lean_object* v_bs_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4236_, v_i_4237_, v_bs_4238_, v___y_4239_, v___y_4241_, v___y_4242_, v___y_4243_);
return v___x_4245_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4236_ = stack[0].m_num;
size_t v_i_4237_ = stack[1].m_num;
lean_object* v_bs_4238_ = stack[2].m_obj;
lean_object* v___y_4239_ = stack[3].m_obj;
lean_object* v___y_4240_ = stack[4].m_obj;
lean_object* v___y_4241_ = stack[5].m_obj;
lean_object* v___y_4242_ = stack[6].m_obj;
lean_object* v___y_4243_ = stack[7].m_obj;
lean_object* v_res_4246_;
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_4236_, v_i_4237_, v_bs_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
stack->m_obj
 = v_res_4246_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___boxed(lean_object* v_sz_4247_, lean_object* v_i_4248_, lean_object* v_bs_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
size_t v_sz_boxed_4256_; size_t v_i_boxed_4257_; lean_object* v_res_4258_; 
v_sz_boxed_4256_ = lean_unbox_usize(v_sz_4247_);
lean_dec(v_sz_4247_);
v_i_boxed_4257_ = lean_unbox_usize(v_i_4248_);
lean_dec(v_i_4248_);
v_res_4258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0(v_sz_boxed_4256_, v_i_boxed_4257_, v_bs_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
return v_res_4258_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(lean_object* v_f_4259_, lean_object* v_v_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
if (lean_obj_tag(v_v_4260_) == 0)
{
lean_object* v_code_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4291_; 
v_code_4267_ = lean_ctor_get(v_v_4260_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v_v_4260_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4269_ = v_v_4260_;
v_isShared_4270_ = v_isSharedCheck_4291_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_code_4267_);
lean_dec(v_v_4260_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4291_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4271_; 
lean_inc(v___y_4265_);
lean_inc_ref(v___y_4264_);
lean_inc(v___y_4263_);
lean_inc_ref(v___y_4262_);
lean_inc(v___y_4261_);
v___x_4271_ = lean_apply_7(v_f_4259_, v_code_4267_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, lean_box(0));
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4282_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4274_ = v___x_4271_;
v_isShared_4275_ = v_isSharedCheck_4282_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4271_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4282_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v_a_4272_);
v___x_4277_ = v___x_4269_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
lean_object* v___x_4279_; 
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 0, v___x_4277_);
v___x_4279_ = v___x_4274_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4277_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_del_object(v___x_4269_);
v_a_4283_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4271_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4271_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
}
else
{
lean_object* v___x_4292_; 
lean_dec_ref(v_f_4259_);
v___x_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4292_, 0, v_v_4260_);
return v___x_4292_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4259_ = stack[0].m_obj;
lean_object* v_v_4260_ = stack[1].m_obj;
lean_object* v___y_4261_ = stack[2].m_obj;
lean_object* v___y_4262_ = stack[3].m_obj;
lean_object* v___y_4263_ = stack[4].m_obj;
lean_object* v___y_4264_ = stack[5].m_obj;
lean_object* v___y_4265_ = stack[6].m_obj;
lean_object* v_res_4293_;
v_res_4293_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4259_, v_v_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
stack->m_obj
 = v_res_4293_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg___boxed(lean_object* v_f_4294_, lean_object* v_v_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4294_, v_v_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
return v_res_4302_;
}
}
lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(uint8_t v_pu_4303_, lean_object* v_f_4304_, lean_object* v_v_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
v___x_4312_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v_f_4304_, v_v_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
return v___x_4312_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_4303_ = stack[0].m_num;
lean_object* v_f_4304_ = stack[1].m_obj;
lean_object* v_v_4305_ = stack[2].m_obj;
lean_object* v___y_4306_ = stack[3].m_obj;
lean_object* v___y_4307_ = stack[4].m_obj;
lean_object* v___y_4308_ = stack[5].m_obj;
lean_object* v___y_4309_ = stack[6].m_obj;
lean_object* v___y_4310_ = stack[7].m_obj;
lean_object* v_res_4313_;
v_res_4313_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_4303_, v_f_4304_, v_v_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
stack->m_obj
 = v_res_4313_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___boxed(lean_object* v_pu_4314_, lean_object* v_f_4315_, lean_object* v_v_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
uint8_t v_pu_boxed_4323_; lean_object* v_res_4324_; 
v_pu_boxed_4323_ = lean_unbox(v_pu_4314_);
v_res_4324_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0(v_pu_boxed_4323_, v_f_4315_, v_v_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
return v_res_4324_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(lean_object* v_decl_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_toSignature_4333_; lean_object* v_value_4334_; uint8_t v_recursive_4335_; lean_object* v_inlineAttr_x3f_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4406_; 
v_toSignature_4333_ = lean_ctor_get(v_decl_4326_, 0);
v_value_4334_ = lean_ctor_get(v_decl_4326_, 1);
v_recursive_4335_ = lean_ctor_get_uint8(v_decl_4326_, sizeof(void*)*3);
v_inlineAttr_x3f_4336_ = lean_ctor_get(v_decl_4326_, 2);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_decl_4326_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4338_ = v_decl_4326_;
v_isShared_4339_ = v_isSharedCheck_4406_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_inlineAttr_x3f_4336_);
lean_inc(v_value_4334_);
lean_inc(v_toSignature_4333_);
lean_dec(v_decl_4326_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4406_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_name_4340_; lean_object* v_type_4341_; lean_object* v_params_4342_; uint8_t v_safe_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4404_; 
v_name_4340_ = lean_ctor_get(v_toSignature_4333_, 0);
v_type_4341_ = lean_ctor_get(v_toSignature_4333_, 2);
v_params_4342_ = lean_ctor_get(v_toSignature_4333_, 3);
v_safe_4343_ = lean_ctor_get_uint8(v_toSignature_4333_, sizeof(void*)*4);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_toSignature_4333_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; 
v_unused_4405_ = lean_ctor_get(v_toSignature_4333_, 1);
lean_dec(v_unused_4405_);
v___x_4345_ = v_toSignature_4333_;
v_isShared_4346_ = v_isSharedCheck_4404_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_params_4342_);
lean_inc(v_type_4341_);
lean_inc(v_name_4340_);
lean_dec(v_toSignature_4333_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4404_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___f_4347_; lean_object* v___x_4348_; 
v___f_4347_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___closed__0));
v___x_4348_ = l_Lean_Compiler_LCNF_toMonoType(v_type_4341_, v_a_4330_, v_a_4331_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; size_t v_sz_4350_; size_t v___x_4351_; lean_object* v___x_4352_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
v_sz_4350_ = lean_array_size(v_params_4342_);
v___x_4351_ = ((size_t)0ULL);
v___x_4352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_FunDecl_toMono_spec__0___redArg(v_sz_4350_, v___x_4351_, v_params_4342_, v_a_4327_, v_a_4329_, v_a_4330_, v_a_4331_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4354_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_spec__0___redArg(v___f_4347_, v_value_4334_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = lean_box(0);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 3, v_a_4353_);
lean_ctor_set(v___x_4345_, 2, v_a_4349_);
lean_ctor_set(v___x_4345_, 1, v___x_4356_);
v___x_4358_ = v___x_4345_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_name_4340_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4379_, 2, v_a_4349_);
lean_ctor_set(v_reuseFailAlloc_4379_, 3, v_a_4353_);
lean_ctor_set_uint8(v_reuseFailAlloc_4379_, sizeof(void*)*4, v_safe_4343_);
v___x_4358_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4360_; 
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 1, v_a_4355_);
lean_ctor_set(v___x_4338_, 0, v___x_4358_);
v___x_4360_ = v___x_4338_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4358_);
lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_a_4355_);
lean_ctor_set(v_reuseFailAlloc_4378_, 2, v_inlineAttr_x3f_4336_);
lean_ctor_set_uint8(v_reuseFailAlloc_4378_, sizeof(void*)*3, v_recursive_4335_);
v___x_4360_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4361_; 
lean_inc_ref(v___x_4360_);
v___x_4361_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_4360_, v_a_4331_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4368_ == 0)
{
lean_object* v_unused_4369_; 
v_unused_4369_ = lean_ctor_get(v___x_4361_, 0);
lean_dec(v_unused_4369_);
v___x_4363_ = v___x_4361_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_dec(v___x_4361_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 0, v___x_4360_);
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4360_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_dec_ref(v___x_4360_);
v_a_4370_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4361_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4361_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4353_);
lean_dec(v_a_4349_);
lean_del_object(v___x_4345_);
lean_dec(v_name_4340_);
lean_del_object(v___x_4338_);
lean_dec(v_inlineAttr_x3f_4336_);
v_a_4380_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4354_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4354_);
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
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_a_4349_);
lean_del_object(v___x_4345_);
lean_dec(v_name_4340_);
lean_del_object(v___x_4338_);
lean_dec(v_inlineAttr_x3f_4336_);
lean_dec_ref(v_value_4334_);
v_a_4388_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4352_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4352_);
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
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_del_object(v___x_4345_);
lean_dec_ref(v_params_4342_);
lean_dec(v_name_4340_);
lean_del_object(v___x_4338_);
lean_dec(v_inlineAttr_x3f_4336_);
lean_dec_ref(v_value_4334_);
v_a_4396_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4348_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4348_);
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
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_4326_ = stack[0].m_obj;
lean_object* v_a_4327_ = stack[1].m_obj;
lean_object* v_a_4328_ = stack[2].m_obj;
lean_object* v_a_4329_ = stack[3].m_obj;
lean_object* v_a_4330_ = stack[4].m_obj;
lean_object* v_a_4331_ = stack[5].m_obj;
lean_object* v_res_4407_;
v_res_4407_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
stack->m_obj
 = v_res_4407_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go___boxed(lean_object* v_decl_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
return v_res_4415_;
}
}
lean_object* l_Lean_Compiler_LCNF_Decl_toMono(lean_object* v_decl_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_){
_start:
{
lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4422_ = l_Lean_instEmptyCollectionFVarIdHashSet;
v___x_4423_ = lean_st_mk_ref(v___x_4422_);
v___x_4424_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_Decl_toMono_go(v_decl_4416_, v___x_4423_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4433_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4433_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4433_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
v___x_4429_ = lean_st_ref_get(v___x_4423_);
lean_dec(v___x_4423_);
lean_dec(v___x_4429_);
if (v_isShared_4428_ == 0)
{
v___x_4431_ = v___x_4427_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4425_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
else
{
lean_dec(v___x_4423_);
return v___x_4424_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Decl_toMono_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_4416_ = stack[0].m_obj;
lean_object* v_a_4417_ = stack[1].m_obj;
lean_object* v_a_4418_ = stack[2].m_obj;
lean_object* v_a_4419_ = stack[3].m_obj;
lean_object* v_a_4420_ = stack[4].m_obj;
lean_object* v_res_4434_;
v_res_4434_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_);
stack->m_obj
 = v_res_4434_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_toMono___boxed(lean_object* v_decl_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_Compiler_LCNF_Decl_toMono(v_decl_4435_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_);
lean_dec(v_a_4439_);
lean_dec_ref(v_a_4438_);
lean_dec(v_a_4437_);
lean_dec_ref(v_a_4436_);
return v_res_4441_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(size_t v_sz_4442_, size_t v_i_4443_, lean_object* v_bs_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
uint8_t v___x_4450_; 
v___x_4450_ = lean_usize_dec_lt(v_i_4443_, v_sz_4442_);
if (v___x_4450_ == 0)
{
lean_object* v___x_4451_; 
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v_bs_4444_);
return v___x_4451_;
}
else
{
lean_object* v_v_4452_; lean_object* v___x_4453_; lean_object* v_bs_x27_4454_; lean_object* v___x_4455_; 
v_v_4452_ = lean_array_uget(v_bs_4444_, v_i_4443_);
v___x_4453_ = lean_unsigned_to_nat(0u);
v_bs_x27_4454_ = lean_array_uset(v_bs_4444_, v_i_4443_, v___x_4453_);
v___x_4455_ = l_Lean_Compiler_LCNF_Decl_toMono(v_v_4452_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; size_t v___x_4457_; size_t v___x_4458_; lean_object* v___x_4459_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = ((size_t)1ULL);
v___x_4458_ = lean_usize_add(v_i_4443_, v___x_4457_);
v___x_4459_ = lean_array_uset(v_bs_x27_4454_, v_i_4443_, v_a_4456_);
v_i_4443_ = v___x_4458_;
v_bs_4444_ = v___x_4459_;
goto _start;
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec_ref(v_bs_x27_4454_);
v_a_4461_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4455_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4455_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4442_ = stack[0].m_num;
size_t v_i_4443_ = stack[1].m_num;
lean_object* v_bs_4444_ = stack[2].m_obj;
lean_object* v___y_4445_ = stack[3].m_obj;
lean_object* v___y_4446_ = stack[4].m_obj;
lean_object* v___y_4447_ = stack[5].m_obj;
lean_object* v___y_4448_ = stack[6].m_obj;
lean_object* v_res_4469_;
v_res_4469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4442_, v_i_4443_, v_bs_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
stack->m_obj
 = v_res_4469_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0___boxed(lean_object* v_sz_4470_, lean_object* v_i_4471_, lean_object* v_bs_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
size_t v_sz_boxed_4478_; size_t v_i_boxed_4479_; lean_object* v_res_4480_; 
v_sz_boxed_4478_ = lean_unbox_usize(v_sz_4470_);
lean_dec(v_sz_4470_);
v_i_boxed_4479_ = lean_unbox_usize(v_i_4471_);
lean_dec(v_i_4471_);
v_res_4480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_boxed_4478_, v_i_boxed_4479_, v_bs_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
return v_res_4480_;
}
}
lean_object* l_Lean_Compiler_LCNF_toMono___lam__0(lean_object* v_x_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
size_t v_sz_4487_; size_t v___x_4488_; lean_object* v___x_4489_; 
v_sz_4487_ = lean_array_size(v_x_4481_);
v___x_4488_ = ((size_t)0ULL);
v___x_4489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toMono_spec__0(v_sz_4487_, v___x_4488_, v_x_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
return v___x_4489_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toMono___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4481_ = stack[0].m_obj;
lean_object* v___y_4482_ = stack[1].m_obj;
lean_object* v___y_4483_ = stack[2].m_obj;
lean_object* v___y_4484_ = stack[3].m_obj;
lean_object* v___y_4485_ = stack[4].m_obj;
lean_object* v_res_4490_;
v_res_4490_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
stack->m_obj
 = v_res_4490_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toMono___lam__0___boxed(lean_object* v_x_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v_res_4497_; 
v_res_4497_ = l_Lean_Compiler_LCNF_toMono___lam__0(v_x_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
lean_dec(v___y_4493_);
lean_dec_ref(v___y_4492_);
return v_res_4497_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4580_; uint8_t v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; 
v___x_4580_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4581_ = 1;
v___x_4582_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_));
v___x_4583_ = l_Lean_registerTraceClass(v___x_4580_, v___x_4581_, v___x_4582_);
return v___x_4583_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4584_;
v_res_4584_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4584_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2____boxed(lean_object* v_a_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l___private_Lean_Compiler_LCNF_ToMono_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToMono_1770774466____hygCtx___hyg_2_();
return v_res_4586_;
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
