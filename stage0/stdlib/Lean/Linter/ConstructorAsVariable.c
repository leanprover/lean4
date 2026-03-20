// Lean compiler output
// Module: Lean.Linter.ConstructorAsVariable
// Imports: public import Lean.Elab.Command public import Lean.Linter.Util
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "constructorNameAsVariable"};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 93, 54, 211, 83, 91, 108, 28)}};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "enable the linter that warns when bound variable names are nullary constructor names"};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 65, 101, 89, 237, 205, 227, 46)}};
static const lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_constructorNameAsVariable;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Local variable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' resembles constructor '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "' - "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "write '."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' (with a dot) or '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' to use the constructor."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_constructorNameAsVariable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_constructorNameAsVariable___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_constructorNameAsVariable___closed__0 = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__0_value;
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 75, 81, 128, 80, 183, 232, 251)}};
static const lean_object* l_Lean_Linter_constructorNameAsVariable___closed__1 = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value;
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__0_value),((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value)}};
static const lean_object* l_Lean_Linter_constructorNameAsVariable___closed__2 = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_constructorNameAsVariable = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__2_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(lean_object* v_o_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; lean_object* v_env_67_; lean_object* v___x_68_; lean_object* v_toEnvExtension_69_; lean_object* v_asyncMode_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v_linterSets_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_66_ = lean_st_ref_get(v___y_64_);
v_env_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc_ref(v_env_67_);
lean_dec(v___x_66_);
v___x_68_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc_ref(v_toEnvExtension_69_);
v_asyncMode_70_ = lean_ctor_get(v_toEnvExtension_69_, 2);
lean_inc(v_asyncMode_70_);
lean_dec_ref(v_toEnvExtension_69_);
v___x_71_ = lean_box(1);
v___x_72_ = lean_box(0);
v_linterSets_73_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_71_, v___x_68_, v_env_67_, v_asyncMode_70_, v___x_72_);
lean_dec(v_asyncMode_70_);
v___x_74_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_74_, 0, v_o_63_);
lean_ctor_set(v___x_74_, 1, v_linterSets_73_);
v___x_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(lean_object* v_o_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_76_, v___y_77_);
lean_dec(v___y_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object* v_o_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_80_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(lean_object* v_o_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(v_o_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object* v_e_90_, lean_object* v___y_91_){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = l_Lean_Expr_hasMVar(v_e_90_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_e_90_);
return v___x_94_;
}
else
{
lean_object* v___x_95_; lean_object* v_mctx_96_; lean_object* v___x_97_; lean_object* v_fst_98_; lean_object* v_snd_99_; lean_object* v___x_100_; lean_object* v_cache_101_; lean_object* v_zetaDeltaFVarIds_102_; lean_object* v_postponed_103_; lean_object* v_diag_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_113_; 
v___x_95_ = lean_st_ref_get(v___y_91_);
v_mctx_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_96_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_instantiateMVarsCore(v_mctx_96_, v_e_90_);
v_fst_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_fst_98_);
v_snd_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc(v_snd_99_);
lean_dec_ref(v___x_97_);
v___x_100_ = lean_st_ref_take(v___y_91_);
v_cache_101_ = lean_ctor_get(v___x_100_, 1);
v_zetaDeltaFVarIds_102_ = lean_ctor_get(v___x_100_, 2);
v_postponed_103_ = lean_ctor_get(v___x_100_, 3);
v_diag_104_ = lean_ctor_get(v___x_100_, 4);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v___x_100_, 0);
lean_dec(v_unused_114_);
v___x_106_ = v___x_100_;
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_diag_104_);
lean_inc(v_postponed_103_);
lean_inc(v_zetaDeltaFVarIds_102_);
lean_inc(v_cache_101_);
lean_dec(v___x_100_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v_snd_99_);
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_snd_99_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_cache_101_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_zetaDeltaFVarIds_102_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_postponed_103_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v_diag_104_);
v___x_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_st_ref_set(v___y_91_, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_111_, 0, v_fst_98_);
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object* v_e_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_e_115_, v___y_116_);
lean_dec(v___y_116_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object* v_e_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_e_119_, v___y_121_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object* v_e_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(v_e_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_132_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(lean_object* v_x1_133_, lean_object* v_x2_134_){
_start:
{
lean_object* v_fst_135_; lean_object* v_fst_136_; lean_object* v_start_137_; lean_object* v_start_138_; uint8_t v___x_139_; 
v_fst_135_ = lean_ctor_get(v_x1_133_, 0);
v_fst_136_ = lean_ctor_get(v_x2_134_, 0);
v_start_137_ = lean_ctor_get(v_fst_135_, 0);
v_start_138_ = lean_ctor_get(v_fst_136_, 0);
v___x_139_ = lean_nat_dec_lt(v_start_137_, v_start_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(lean_object* v_x1_140_, lean_object* v_x2_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v_x1_140_, v_x2_141_);
lean_dec_ref(v_x2_141_);
lean_dec_ref(v_x1_140_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(lean_object* v_as_145_, lean_object* v_lo_146_, lean_object* v_hi_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_nat_dec_lt(v_lo_146_, v_hi_147_);
if (v___x_148_ == 0)
{
lean_dec(v_lo_146_);
return v_as_145_;
}
else
{
lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v_fst_151_; lean_object* v_snd_152_; uint8_t v___x_153_; 
v___f_149_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___closed__0));
lean_inc(v_lo_146_);
v___x_150_ = l_Array_qpartition___redArg(v_as_145_, v___f_149_, v_lo_146_, v_hi_147_);
v_fst_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_fst_151_);
v_snd_152_ = lean_ctor_get(v___x_150_, 1);
lean_inc(v_snd_152_);
lean_dec_ref(v___x_150_);
v___x_153_ = lean_nat_dec_le(v_hi_147_, v_fst_151_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_snd_152_, v_lo_146_, v_fst_151_);
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_fst_151_, v___x_155_);
lean_dec(v_fst_151_);
v_as_145_ = v___x_154_;
v_lo_146_ = v___x_156_;
goto _start;
}
else
{
lean_dec(v_fst_151_);
lean_dec(v_lo_146_);
return v_snd_152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(lean_object* v_as_158_, lean_object* v_lo_159_, lean_object* v_hi_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_as_158_, v_lo_159_, v_hi_160_);
lean_dec(v_hi_160_);
return v_res_161_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(uint8_t v___y_163_, uint8_t v_suppressElabErrors_164_, lean_object* v_x_165_){
_start:
{
if (lean_obj_tag(v_x_165_) == 1)
{
lean_object* v_pre_166_; 
v_pre_166_ = lean_ctor_get(v_x_165_, 0);
if (lean_obj_tag(v_pre_166_) == 0)
{
lean_object* v_str_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_167_ = lean_ctor_get(v_x_165_, 1);
v___x_168_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0));
v___x_169_ = lean_string_dec_eq(v_str_167_, v___x_168_);
if (v___x_169_ == 0)
{
return v___y_163_;
}
else
{
return v_suppressElabErrors_164_;
}
}
else
{
return v___y_163_;
}
}
else
{
return v___y_163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed(lean_object* v___y_170_, lean_object* v_suppressElabErrors_171_, lean_object* v_x_172_){
_start:
{
uint8_t v___y_23329__boxed_173_; uint8_t v_suppressElabErrors_boxed_174_; uint8_t v_res_175_; lean_object* v_r_176_; 
v___y_23329__boxed_173_ = lean_unbox(v___y_170_);
v_suppressElabErrors_boxed_174_ = lean_unbox(v_suppressElabErrors_171_);
v_res_175_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_23329__boxed_173_, v_suppressElabErrors_boxed_174_, v_x_172_);
lean_dec(v_x_172_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(lean_object* v_opts_177_, lean_object* v_opt_178_){
_start:
{
lean_object* v_name_179_; lean_object* v_defValue_180_; lean_object* v_map_181_; lean_object* v___x_182_; 
v_name_179_ = lean_ctor_get(v_opt_178_, 0);
v_defValue_180_ = lean_ctor_get(v_opt_178_, 1);
v_map_181_ = lean_ctor_get(v_opts_177_, 0);
v___x_182_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_181_, v_name_179_);
if (lean_obj_tag(v___x_182_) == 0)
{
uint8_t v___x_183_; 
v___x_183_ = lean_unbox(v_defValue_180_);
return v___x_183_;
}
else
{
lean_object* v_val_184_; 
v_val_184_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_val_184_);
lean_dec_ref(v___x_182_);
if (lean_obj_tag(v_val_184_) == 1)
{
uint8_t v_v_185_; 
v_v_185_ = lean_ctor_get_uint8(v_val_184_, 0);
lean_dec_ref(v_val_184_);
return v_v_185_;
}
else
{
uint8_t v___x_186_; 
lean_dec(v_val_184_);
v___x_186_ = lean_unbox(v_defValue_180_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(lean_object* v_opts_187_, lean_object* v_opt_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_187_, v_opt_188_);
lean_dec_ref(v_opt_188_);
lean_dec_ref(v_opts_187_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_191_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
lean_ctor_set(v___x_196_, 2, v___x_195_);
lean_ctor_set(v___x_196_, 3, v___x_194_);
lean_ctor_set(v___x_196_, 4, v___x_194_);
lean_ctor_set(v___x_196_, 5, v___x_194_);
lean_ctor_set(v___x_196_, 6, v___x_194_);
lean_ctor_set(v___x_196_, 7, v___x_194_);
lean_ctor_set(v___x_196_, 8, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(32u);
v___x_198_ = lean_mk_empty_array_with_capacity(v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4(void){
_start:
{
size_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_200_ = ((size_t)5ULL);
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = lean_unsigned_to_nat(32u);
v___x_203_ = lean_mk_empty_array_with_capacity(v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3);
v___x_205_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
lean_ctor_set(v___x_205_, 2, v___x_201_);
lean_ctor_set(v___x_205_, 3, v___x_201_);
lean_ctor_set_usize(v___x_205_, 4, v___x_200_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_206_ = lean_box(1);
v___x_207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4);
v___x_208_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_207_);
lean_ctor_set(v___x_209_, 2, v___x_206_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(lean_object* v_msgData_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; lean_object* v_env_214_; lean_object* v___x_215_; lean_object* v_scopes_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_opts_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_213_ = lean_st_ref_get(v___y_211_);
v_env_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc_ref(v_env_214_);
lean_dec(v___x_213_);
v___x_215_ = lean_st_ref_get(v___y_211_);
v_scopes_216_ = lean_ctor_get(v___x_215_, 2);
lean_inc(v_scopes_216_);
lean_dec(v___x_215_);
v___x_217_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_218_ = l_List_head_x21___redArg(v___x_217_, v_scopes_216_);
lean_dec(v_scopes_216_);
v_opts_219_ = lean_ctor_get(v___x_218_, 1);
lean_inc_ref(v_opts_219_);
lean_dec(v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2);
v___x_221_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5);
v___x_222_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_222_, 0, v_env_214_);
lean_ctor_set(v___x_222_, 1, v___x_220_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
lean_ctor_set(v___x_222_, 3, v_opts_219_);
v___x_223_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
lean_ctor_set(v___x_223_, 1, v_msgData_210_);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(lean_object* v_msgData_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_225_, v___y_226_);
lean_dec(v___y_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(lean_object* v_ref_230_, lean_object* v_msgData_231_, uint8_t v_severity_232_, uint8_t v_isSilent_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___y_238_; lean_object* v___y_239_; lean_object* v___y_240_; uint8_t v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; uint8_t v___y_301_; uint8_t v___y_302_; uint8_t v___y_303_; lean_object* v___y_304_; lean_object* v___y_305_; uint8_t v___y_329_; uint8_t v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; uint8_t v___y_337_; uint8_t v___y_338_; uint8_t v___y_339_; uint8_t v___x_354_; uint8_t v___y_356_; uint8_t v___y_357_; uint8_t v___y_358_; uint8_t v___y_360_; uint8_t v___x_372_; 
v___x_354_ = 2;
v___x_372_ = l_Lean_instBEqMessageSeverity_beq(v_severity_232_, v___x_354_);
if (v___x_372_ == 0)
{
v___y_360_ = v___x_372_;
goto v___jp_359_;
}
else
{
uint8_t v___x_373_; 
lean_inc_ref(v_msgData_231_);
v___x_373_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_231_);
v___y_360_ = v___x_373_;
goto v___jp_359_;
}
v___jp_237_:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Elab_Command_getScope___redArg(v___y_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_248_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_a_247_);
lean_dec_ref(v___x_246_);
v___x_248_ = l_Lean_Elab_Command_getScope___redArg(v___y_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_283_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_283_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_283_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_283_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v_currNamespace_254_; lean_object* v_openDecls_255_; lean_object* v_env_256_; lean_object* v_messages_257_; lean_object* v_scopes_258_; lean_object* v_usedQuotCtxts_259_; lean_object* v_nextMacroScope_260_; lean_object* v_maxRecDepth_261_; lean_object* v_ngen_262_; lean_object* v_auxDeclNGen_263_; lean_object* v_infoState_264_; lean_object* v_traceState_265_; lean_object* v_snapshotTasks_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_282_; 
v___x_253_ = lean_st_ref_take(v___y_245_);
v_currNamespace_254_ = lean_ctor_get(v_a_247_, 2);
lean_inc(v_currNamespace_254_);
lean_dec(v_a_247_);
v_openDecls_255_ = lean_ctor_get(v_a_249_, 3);
lean_inc(v_openDecls_255_);
lean_dec(v_a_249_);
v_env_256_ = lean_ctor_get(v___x_253_, 0);
v_messages_257_ = lean_ctor_get(v___x_253_, 1);
v_scopes_258_ = lean_ctor_get(v___x_253_, 2);
v_usedQuotCtxts_259_ = lean_ctor_get(v___x_253_, 3);
v_nextMacroScope_260_ = lean_ctor_get(v___x_253_, 4);
v_maxRecDepth_261_ = lean_ctor_get(v___x_253_, 5);
v_ngen_262_ = lean_ctor_get(v___x_253_, 6);
v_auxDeclNGen_263_ = lean_ctor_get(v___x_253_, 7);
v_infoState_264_ = lean_ctor_get(v___x_253_, 8);
v_traceState_265_ = lean_ctor_get(v___x_253_, 9);
v_snapshotTasks_266_ = lean_ctor_get(v___x_253_, 10);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_282_ == 0)
{
v___x_268_ = v___x_253_;
v_isShared_269_ = v_isSharedCheck_282_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_snapshotTasks_266_);
lean_inc(v_traceState_265_);
lean_inc(v_infoState_264_);
lean_inc(v_auxDeclNGen_263_);
lean_inc(v_ngen_262_);
lean_inc(v_maxRecDepth_261_);
lean_inc(v_nextMacroScope_260_);
lean_inc(v_usedQuotCtxts_259_);
lean_inc(v_scopes_258_);
lean_inc(v_messages_257_);
lean_inc(v_env_256_);
lean_dec(v___x_253_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_282_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v_currNamespace_254_);
lean_ctor_set(v___x_270_, 1, v_openDecls_255_);
v___x_271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___y_244_);
v___x_272_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_272_, 0, v___y_240_);
lean_ctor_set(v___x_272_, 1, v___y_242_);
lean_ctor_set(v___x_272_, 2, v___y_243_);
lean_ctor_set(v___x_272_, 3, v___y_239_);
lean_ctor_set(v___x_272_, 4, v___x_271_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*5, v___y_241_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*5 + 1, v___y_238_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*5 + 2, v_isSilent_233_);
v___x_273_ = l_Lean_MessageLog_add(v___x_272_, v_messages_257_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___x_273_);
v___x_275_ = v___x_268_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_env_256_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_scopes_258_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_usedQuotCtxts_259_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_nextMacroScope_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_maxRecDepth_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_ngen_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v_auxDeclNGen_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_infoState_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 9, v_traceState_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 10, v_snapshotTasks_266_);
v___x_275_ = v_reuseFailAlloc_281_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_st_ref_set(v___y_245_, v___x_275_);
v___x_277_ = lean_box(0);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_277_);
v___x_279_ = v___x_251_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_a_247_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec_ref(v___y_240_);
lean_dec_ref(v___y_239_);
v_a_284_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_248_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_248_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec_ref(v___y_240_);
lean_dec_ref(v___y_239_);
v_a_292_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_246_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_246_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
v___jp_300_:
{
lean_object* v_fileName_306_; lean_object* v_fileMap_307_; uint8_t v_suppressElabErrors_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_327_; 
v_fileName_306_ = lean_ctor_get(v___y_234_, 0);
lean_inc_ref(v_fileName_306_);
v_fileMap_307_ = lean_ctor_get(v___y_234_, 1);
lean_inc_ref(v_fileMap_307_);
v_suppressElabErrors_308_ = lean_ctor_get_uint8(v___y_234_, sizeof(void*)*10);
lean_dec_ref(v___y_234_);
v___x_309_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_231_);
v___x_310_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_309_, v___y_235_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_327_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_327_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_327_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
lean_inc_ref(v_fileMap_307_);
v___x_315_ = l_Lean_FileMap_toPosition(v_fileMap_307_, v___y_304_);
lean_dec(v___y_304_);
v___x_316_ = l_Lean_FileMap_toPosition(v_fileMap_307_, v___y_305_);
lean_dec(v___y_305_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_308_ == 0)
{
lean_del_object(v___x_313_);
v___y_238_ = v___y_302_;
v___y_239_ = v___x_318_;
v___y_240_ = v_fileName_306_;
v___y_241_ = v___y_303_;
v___y_242_ = v___x_315_;
v___y_243_ = v___x_317_;
v___y_244_ = v_a_311_;
v___y_245_ = v___y_235_;
goto v___jp_237_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___f_321_; uint8_t v___x_322_; 
v___x_319_ = lean_box(v___y_301_);
v___x_320_ = lean_box(v_suppressElabErrors_308_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed), 3, 2);
lean_closure_set(v___f_321_, 0, v___x_319_);
lean_closure_set(v___f_321_, 1, v___x_320_);
lean_inc(v_a_311_);
v___x_322_ = l_Lean_MessageData_hasTag(v___f_321_, v_a_311_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_325_; 
lean_dec_ref(v___x_317_);
lean_dec_ref(v___x_315_);
lean_dec(v_a_311_);
lean_dec_ref(v_fileName_306_);
v___x_323_ = lean_box(0);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_323_);
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
else
{
lean_del_object(v___x_313_);
v___y_238_ = v___y_302_;
v___y_239_ = v___x_318_;
v___y_240_ = v_fileName_306_;
v___y_241_ = v___y_303_;
v___y_242_ = v___x_315_;
v___y_243_ = v___x_317_;
v___y_244_ = v_a_311_;
v___y_245_ = v___y_235_;
goto v___jp_237_;
}
}
}
}
v___jp_328_:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Syntax_getTailPos_x3f(v___y_332_, v___y_331_);
lean_dec(v___y_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_inc(v___y_333_);
v___y_301_ = v___y_329_;
v___y_302_ = v___y_330_;
v___y_303_ = v___y_331_;
v___y_304_ = v___y_333_;
v___y_305_ = v___y_333_;
goto v___jp_300_;
}
else
{
lean_object* v_val_335_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref(v___x_334_);
v___y_301_ = v___y_329_;
v___y_302_ = v___y_330_;
v___y_303_ = v___y_331_;
v___y_304_ = v___y_333_;
v___y_305_ = v_val_335_;
goto v___jp_300_;
}
}
v___jp_336_:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Elab_Command_getRef___redArg(v___y_234_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v_ref_342_; lean_object* v___x_343_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
v_ref_342_ = l_Lean_replaceRef(v_ref_230_, v_a_341_);
lean_dec(v_a_341_);
v___x_343_ = l_Lean_Syntax_getPos_x3f(v_ref_342_, v___y_338_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___y_329_ = v___y_337_;
v___y_330_ = v___y_339_;
v___y_331_ = v___y_338_;
v___y_332_ = v_ref_342_;
v___y_333_ = v___x_344_;
goto v___jp_328_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_val_345_);
lean_dec_ref(v___x_343_);
v___y_329_ = v___y_337_;
v___y_330_ = v___y_339_;
v___y_331_ = v___y_338_;
v___y_332_ = v_ref_342_;
v___y_333_ = v_val_345_;
goto v___jp_328_;
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___y_234_);
lean_dec_ref(v_msgData_231_);
v_a_346_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_340_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_340_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
v___jp_355_:
{
if (v___y_358_ == 0)
{
v___y_337_ = v___y_356_;
v___y_338_ = v___y_357_;
v___y_339_ = v_severity_232_;
goto v___jp_336_;
}
else
{
v___y_337_ = v___y_356_;
v___y_338_ = v___y_357_;
v___y_339_ = v___x_354_;
goto v___jp_336_;
}
}
v___jp_359_:
{
if (v___y_360_ == 0)
{
lean_object* v___x_361_; lean_object* v_scopes_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_opts_365_; uint8_t v___x_366_; uint8_t v___x_367_; 
v___x_361_ = lean_st_ref_get(v___y_235_);
v_scopes_362_ = lean_ctor_get(v___x_361_, 2);
lean_inc(v_scopes_362_);
lean_dec(v___x_361_);
v___x_363_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_364_ = l_List_head_x21___redArg(v___x_363_, v_scopes_362_);
lean_dec(v_scopes_362_);
v_opts_365_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref(v_opts_365_);
lean_dec(v___x_364_);
v___x_366_ = 1;
v___x_367_ = l_Lean_instBEqMessageSeverity_beq(v_severity_232_, v___x_366_);
if (v___x_367_ == 0)
{
lean_dec_ref(v_opts_365_);
v___y_356_ = v___y_360_;
v___y_357_ = v___y_360_;
v___y_358_ = v___x_367_;
goto v___jp_355_;
}
else
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = l_Lean_warningAsError;
v___x_369_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_365_, v___x_368_);
lean_dec_ref(v_opts_365_);
v___y_356_ = v___y_360_;
v___y_357_ = v___y_360_;
v___y_358_ = v___x_369_;
goto v___jp_355_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; 
lean_dec_ref(v___y_234_);
lean_dec_ref(v_msgData_231_);
v___x_370_ = lean_box(0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object* v_ref_374_, lean_object* v_msgData_375_, lean_object* v_severity_376_, lean_object* v_isSilent_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v_severity_boxed_381_; uint8_t v_isSilent_boxed_382_; lean_object* v_res_383_; 
v_severity_boxed_381_ = lean_unbox(v_severity_376_);
v_isSilent_boxed_382_ = lean_unbox(v_isSilent_377_);
v_res_383_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_374_, v_msgData_375_, v_severity_boxed_381_, v_isSilent_boxed_382_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec(v_ref_374_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object* v_ref_384_, lean_object* v_msgData_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
uint8_t v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; 
v___x_389_ = 1;
v___x_390_ = 0;
v___x_391_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_384_, v_msgData_385_, v___x_389_, v___x_390_, v___y_386_, v___y_387_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object* v_ref_392_, lean_object* v_msgData_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_392_, v_msgData_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec(v_ref_392_);
return v_res_397_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2));
v___x_403_ = l_Lean_stringToMessageData(v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* v_linterOption_404_, lean_object* v_stx_405_, lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_name_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_425_; 
v_name_410_ = lean_ctor_get(v_linterOption_404_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_linterOption_404_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v_linterOption_404_, 1);
lean_dec(v_unused_426_);
v___x_412_ = v_linterOption_404_;
v_isShared_413_ = v_isSharedCheck_425_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_name_410_);
lean_dec(v_linterOption_404_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_425_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
lean_inc(v_name_410_);
v___x_415_ = l_Lean_MessageData_ofName(v_name_410_);
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 7);
lean_ctor_set(v___x_412_, 1, v___x_415_);
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_424_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_disable_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_418_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v_disable_420_ = l_Lean_MessageData_note(v___x_419_);
v___x_421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_421_, 0, v_msg_406_);
lean_ctor_set(v___x_421_, 1, v_disable_420_);
v___x_422_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_422_, 0, v_name_410_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_405_, v___x_422_, v___y_407_, v___y_408_);
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_427_, lean_object* v_stx_428_, lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_427_, v_stx_428_, v_msg_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec(v_stx_428_);
return v_res_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_452_, size_t v_sz_453_, size_t v_i_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec_ref(v___y_456_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_b_455_);
return v___x_460_;
}
else
{
lean_object* v_a_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_507_; 
v_a_461_ = lean_array_uget(v_as_452_, v_i_454_);
v_snd_462_ = lean_ctor_get(v_a_461_, 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_461_);
if (v_isSharedCheck_507_ == 0)
{
lean_object* v_unused_508_; 
v_unused_508_ = lean_ctor_get(v_a_461_, 0);
lean_dec(v_unused_508_);
v___x_464_ = v_a_461_;
v_isShared_465_ = v_isSharedCheck_507_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_dec(v_a_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_507_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_snd_466_; lean_object* v_fst_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_506_; 
v_snd_466_ = lean_ctor_get(v_snd_462_, 1);
v_fst_467_ = lean_ctor_get(v_snd_462_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_snd_462_);
if (v_isSharedCheck_506_ == 0)
{
v___x_469_ = v_snd_462_;
v_isShared_470_ = v_isSharedCheck_506_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_467_);
lean_dec(v_snd_462_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_506_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v_fst_471_; lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_505_; 
v_fst_471_ = lean_ctor_get(v_snd_466_, 0);
v_snd_472_ = lean_ctor_get(v_snd_466_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_snd_466_);
if (v_isSharedCheck_505_ == 0)
{
v___x_474_ = v_snd_466_;
v_isShared_475_ = v_isSharedCheck_505_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_inc(v_fst_471_);
lean_dec(v_snd_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_505_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_476_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_478_ = l_Lean_MessageData_ofName(v_fst_471_);
lean_inc_ref(v___x_478_);
if (v_isShared_475_ == 0)
{
lean_ctor_set_tag(v___x_474_, 7);
lean_ctor_set(v___x_474_, 1, v___x_478_);
lean_ctor_set(v___x_474_, 0, v___x_477_);
v___x_480_ = v___x_474_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_478_);
v___x_480_ = v_reuseFailAlloc_504_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_470_ == 0)
{
lean_ctor_set_tag(v___x_469_, 7);
lean_ctor_set(v___x_469_, 1, v___x_481_);
lean_ctor_set(v___x_469_, 0, v___x_480_);
v___x_483_ = v___x_469_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_503_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = l_Lean_MessageData_ofName(v_snd_472_);
lean_inc_ref(v___x_484_);
if (v_isShared_465_ == 0)
{
lean_ctor_set_tag(v___x_464_, 7);
lean_ctor_set(v___x_464_, 1, v___x_484_);
lean_ctor_set(v___x_464_, 0, v___x_483_);
v___x_486_ = v___x_464_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_502_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_487_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_478_);
v___x_491_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_484_);
v___x_494_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_488_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
lean_inc_ref(v___y_456_);
v___x_497_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_476_, v_fst_467_, v___x_496_, v___y_456_, v___y_457_);
lean_dec(v_fst_467_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; 
lean_dec_ref(v___x_497_);
v___x_498_ = lean_box(0);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_454_, v___x_499_);
v_i_454_ = v___x_500_;
v_b_455_ = v___x_498_;
goto _start;
}
else
{
lean_dec_ref(v___y_456_);
return v___x_497_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_509_, lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_517_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_509_, v_sz_boxed_516_, v_i_boxed_517_, v_b_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v_as_509_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_box(v___x_519_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_528_, lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
uint8_t v___x_23939__boxed_535_; lean_object* v_res_536_; 
v___x_23939__boxed_535_ = lean_unbox(v___x_528_);
v_res_536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_23939__boxed_535_, v_x_529_, v_x_530_, v_x_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v_x_531_);
lean_dec_ref(v_x_530_);
lean_dec_ref(v_x_529_);
return v_res_536_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
uint8_t v___x_539_; 
v___x_539_ = 0;
return v___x_539_;
}
else
{
lean_object* v_key_540_; lean_object* v_tail_541_; uint8_t v___x_542_; 
v_key_540_ = lean_ctor_get(v_x_538_, 0);
v_tail_541_ = lean_ctor_get(v_x_538_, 2);
v___x_542_ = l_Lean_Syntax_instBEqRange_beq(v_key_540_, v_a_537_);
if (v___x_542_ == 0)
{
v_x_538_ = v_tail_541_;
goto _start;
}
else
{
return v___x_542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_544_, lean_object* v_x_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_544_, v_x_545_);
lean_dec(v_x_545_);
lean_dec_ref(v_a_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_buckets_550_; lean_object* v___x_551_; uint64_t v___x_552_; uint64_t v___x_553_; uint64_t v___x_554_; uint64_t v_fold_555_; uint64_t v___x_556_; uint64_t v___x_557_; uint64_t v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_buckets_550_ = lean_ctor_get(v_m_548_, 1);
v___x_551_ = lean_array_get_size(v_buckets_550_);
v___x_552_ = l_Lean_Syntax_instHashableRange_hash(v_a_549_);
v___x_553_ = 32ULL;
v___x_554_ = lean_uint64_shift_right(v___x_552_, v___x_553_);
v_fold_555_ = lean_uint64_xor(v___x_552_, v___x_554_);
v___x_556_ = 16ULL;
v___x_557_ = lean_uint64_shift_right(v_fold_555_, v___x_556_);
v___x_558_ = lean_uint64_xor(v_fold_555_, v___x_557_);
v___x_559_ = lean_uint64_to_usize(v___x_558_);
v___x_560_ = lean_usize_of_nat(v___x_551_);
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_sub(v___x_560_, v___x_561_);
v___x_563_ = lean_usize_land(v___x_559_, v___x_562_);
v___x_564_ = lean_array_uget_borrowed(v_buckets_550_, v___x_563_);
v___x_565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_549_, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_566_, v_a_567_);
lean_dec_ref(v_a_567_);
lean_dec_ref(v_m_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_570_, lean_object* v_b_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_dec(v_b_571_);
lean_dec_ref(v_a_570_);
return v_x_572_;
}
else
{
lean_object* v_key_573_; lean_object* v_value_574_; lean_object* v_tail_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_587_; 
v_key_573_ = lean_ctor_get(v_x_572_, 0);
v_value_574_ = lean_ctor_get(v_x_572_, 1);
v_tail_575_ = lean_ctor_get(v_x_572_, 2);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_587_ == 0)
{
v___x_577_ = v_x_572_;
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_tail_575_);
lean_inc(v_value_574_);
lean_inc(v_key_573_);
lean_dec(v_x_572_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_Syntax_instBEqRange_beq(v_key_573_, v_a_570_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_570_, v_b_571_, v_tail_575_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 2, v___x_580_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_key_573_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_value_574_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v_value_574_);
lean_dec(v_key_573_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_b_571_);
lean_ctor_set(v___x_577_, 0, v_a_570_);
v___x_585_ = v___x_577_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_570_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_b_571_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_tail_575_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
return v_x_588_;
}
else
{
lean_object* v_key_590_; lean_object* v_value_591_; lean_object* v_tail_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_615_; 
v_key_590_ = lean_ctor_get(v_x_589_, 0);
v_value_591_ = lean_ctor_get(v_x_589_, 1);
v_tail_592_ = lean_ctor_get(v_x_589_, 2);
v_isSharedCheck_615_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_615_ == 0)
{
v___x_594_ = v_x_589_;
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_tail_592_);
lean_inc(v_value_591_);
lean_inc(v_key_590_);
lean_dec(v_x_589_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_615_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; uint64_t v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v_fold_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_596_ = lean_array_get_size(v_x_588_);
v___x_597_ = l_Lean_Syntax_instHashableRange_hash(v_key_590_);
v___x_598_ = 32ULL;
v___x_599_ = lean_uint64_shift_right(v___x_597_, v___x_598_);
v_fold_600_ = lean_uint64_xor(v___x_597_, v___x_599_);
v___x_601_ = 16ULL;
v___x_602_ = lean_uint64_shift_right(v_fold_600_, v___x_601_);
v___x_603_ = lean_uint64_xor(v_fold_600_, v___x_602_);
v___x_604_ = lean_uint64_to_usize(v___x_603_);
v___x_605_ = lean_usize_of_nat(v___x_596_);
v___x_606_ = ((size_t)1ULL);
v___x_607_ = lean_usize_sub(v___x_605_, v___x_606_);
v___x_608_ = lean_usize_land(v___x_604_, v___x_607_);
v___x_609_ = lean_array_uget_borrowed(v_x_588_, v___x_608_);
lean_inc(v___x_609_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 2, v___x_609_);
v___x_611_ = v___x_594_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_key_590_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_value_591_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v___x_609_);
v___x_611_ = v_reuseFailAlloc_614_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_array_uset(v_x_588_, v___x_608_, v___x_611_);
v_x_588_ = v___x_612_;
v_x_589_ = v_tail_592_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_616_, lean_object* v_source_617_, lean_object* v_target_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = lean_array_get_size(v_source_617_);
v___x_620_ = lean_nat_dec_lt(v_i_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref(v_source_617_);
lean_dec(v_i_616_);
return v_target_618_;
}
else
{
lean_object* v_es_621_; lean_object* v___x_622_; lean_object* v_source_623_; lean_object* v_target_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_es_621_ = lean_array_fget(v_source_617_, v_i_616_);
v___x_622_ = lean_box(0);
v_source_623_ = lean_array_fset(v_source_617_, v_i_616_, v___x_622_);
v_target_624_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_618_, v_es_621_);
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = lean_nat_add(v_i_616_, v___x_625_);
lean_dec(v_i_616_);
v_i_616_ = v___x_626_;
v_source_617_ = v_source_623_;
v_target_618_ = v_target_624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_nbuckets_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_629_ = lean_array_get_size(v_data_628_);
v___x_630_ = lean_unsigned_to_nat(2u);
v_nbuckets_631_ = lean_nat_mul(v___x_629_, v___x_630_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_box(0);
v___x_634_ = lean_mk_array(v_nbuckets_631_, v___x_633_);
v___x_635_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_632_, v_data_628_, v___x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_636_, lean_object* v_a_637_, lean_object* v_b_638_){
_start:
{
lean_object* v_size_639_; lean_object* v_buckets_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_683_; 
v_size_639_ = lean_ctor_get(v_m_636_, 0);
v_buckets_640_ = lean_ctor_get(v_m_636_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_m_636_);
if (v_isSharedCheck_683_ == 0)
{
v___x_642_ = v_m_636_;
v_isShared_643_ = v_isSharedCheck_683_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_buckets_640_);
lean_inc(v_size_639_);
lean_dec(v_m_636_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_683_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; uint64_t v_fold_648_; uint64_t v___x_649_; uint64_t v___x_650_; uint64_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; lean_object* v_bkt_657_; uint8_t v___x_658_; 
v___x_644_ = lean_array_get_size(v_buckets_640_);
v___x_645_ = l_Lean_Syntax_instHashableRange_hash(v_a_637_);
v___x_646_ = 32ULL;
v___x_647_ = lean_uint64_shift_right(v___x_645_, v___x_646_);
v_fold_648_ = lean_uint64_xor(v___x_645_, v___x_647_);
v___x_649_ = 16ULL;
v___x_650_ = lean_uint64_shift_right(v_fold_648_, v___x_649_);
v___x_651_ = lean_uint64_xor(v_fold_648_, v___x_650_);
v___x_652_ = lean_uint64_to_usize(v___x_651_);
v___x_653_ = lean_usize_of_nat(v___x_644_);
v___x_654_ = ((size_t)1ULL);
v___x_655_ = lean_usize_sub(v___x_653_, v___x_654_);
v___x_656_ = lean_usize_land(v___x_652_, v___x_655_);
v_bkt_657_ = lean_array_uget_borrowed(v_buckets_640_, v___x_656_);
v___x_658_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_637_, v_bkt_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v_size_x27_660_; lean_object* v___x_661_; lean_object* v_buckets_x27_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v_size_x27_660_ = lean_nat_add(v_size_639_, v___x_659_);
lean_dec(v_size_639_);
lean_inc(v_bkt_657_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v_a_637_);
lean_ctor_set(v___x_661_, 1, v_b_638_);
lean_ctor_set(v___x_661_, 2, v_bkt_657_);
v_buckets_x27_662_ = lean_array_uset(v_buckets_640_, v___x_656_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_mul(v_size_x27_660_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(3u);
v___x_666_ = lean_nat_div(v___x_664_, v___x_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_array_get_size(v_buckets_x27_662_);
v___x_668_ = lean_nat_dec_le(v___x_666_, v___x_667_);
lean_dec(v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v_val_669_; lean_object* v___x_671_; 
v_val_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_662_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_val_669_);
lean_ctor_set(v___x_642_, 0, v_size_x27_660_);
v___x_671_ = v___x_642_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_size_x27_660_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_val_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_674_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v_buckets_x27_662_);
lean_ctor_set(v___x_642_, 0, v_size_x27_660_);
v___x_674_ = v___x_642_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_size_x27_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_buckets_x27_662_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v___x_676_; lean_object* v_buckets_x27_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc(v_bkt_657_);
v___x_676_ = lean_box(0);
v_buckets_x27_677_ = lean_array_uset(v_buckets_640_, v___x_656_, v___x_676_);
v___x_678_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_637_, v_b_638_, v_bkt_657_);
v___x_679_ = lean_array_uset(v_buckets_x27_677_, v___x_656_, v___x_678_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 1, v___x_679_);
v___x_681_ = v___x_642_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_639_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_684_, lean_object* v_val_685_, lean_object* v_info_686_, lean_object* v___x_687_, lean_object* v_val_688_, uint8_t v___x_689_, lean_object* v_as_x27_690_, lean_object* v_b_691_, lean_object* v___y_692_){
_start:
{
if (lean_obj_tag(v_as_x27_690_) == 0)
{
lean_object* v___x_694_; 
lean_dec_ref(v_val_688_);
lean_dec(v___x_687_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v_b_691_);
return v___x_694_;
}
else
{
lean_object* v_head_695_; lean_object* v_tail_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_724_; 
v_head_695_ = lean_ctor_get(v_as_x27_690_, 0);
v_tail_696_ = lean_ctor_get(v_as_x27_690_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_as_x27_690_);
if (v_isSharedCheck_724_ == 0)
{
v___x_698_ = v_as_x27_690_;
v_isShared_699_ = v_isSharedCheck_724_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_tail_696_);
lean_inc(v_head_695_);
lean_dec(v_as_x27_690_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_724_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v_env_701_; lean_object* v___x_702_; lean_object* v___x_717_; 
v___x_700_ = lean_st_ref_get(v___y_692_);
v_env_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc_ref(v_env_701_);
lean_dec(v___x_700_);
v___x_702_ = lean_box(0);
lean_inc(v_head_695_);
v___x_717_ = l_Lean_Environment_find_x3f(v_env_701_, v_head_695_, v___x_689_);
if (lean_obj_tag(v___x_717_) == 1)
{
lean_object* v_val_718_; 
v_val_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_val_718_);
lean_dec_ref(v___x_717_);
if (lean_obj_tag(v_val_718_) == 6)
{
lean_object* v_val_719_; lean_object* v_numFields_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_val_719_ = lean_ctor_get(v_val_718_, 0);
lean_inc_ref(v_val_719_);
lean_dec_ref(v_val_718_);
v_numFields_720_ = lean_ctor_get(v_val_719_, 4);
lean_inc(v_numFields_720_);
lean_dec_ref(v_val_719_);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_nat_dec_lt(v___x_721_, v_numFields_720_);
lean_dec(v_numFields_720_);
if (v___x_722_ == 0)
{
goto v___jp_703_;
}
else
{
lean_del_object(v___x_698_);
lean_dec(v_head_695_);
v_as_x27_690_ = v_tail_696_;
v_b_691_ = v___x_702_;
goto _start;
}
}
else
{
lean_dec(v_val_718_);
goto v___jp_703_;
}
}
else
{
lean_dec(v___x_717_);
goto v___jp_703_;
}
v___jp_703_:
{
if (lean_obj_tag(v_head_695_) == 1)
{
lean_object* v_str_704_; uint8_t v___x_705_; 
v_str_704_ = lean_ctor_get(v_head_695_, 1);
v___x_705_ = lean_string_dec_eq(v_str_704_, v_str_684_);
if (v___x_705_ == 0)
{
lean_dec_ref(v_head_695_);
lean_del_object(v___x_698_);
v_as_x27_690_ = v_tail_696_;
v_b_691_ = v___x_702_;
goto _start;
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = lean_st_ref_take(v_val_685_);
v___x_708_ = l_Lean_Elab_Info_stx(v_info_686_);
lean_inc(v___x_687_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 0);
lean_ctor_set(v___x_698_, 1, v_head_695_);
lean_ctor_set(v___x_698_, 0, v___x_687_);
v___x_710_ = v___x_698_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_head_695_);
v___x_710_ = v_reuseFailAlloc_715_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_708_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_inc_ref(v_val_688_);
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_707_, v_val_688_, v___x_711_);
v___x_713_ = lean_st_ref_set(v_val_685_, v___x_712_);
v_as_x27_690_ = v_tail_696_;
v_b_691_ = v___x_702_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_698_);
lean_dec(v_head_695_);
v_as_x27_690_ = v_tail_696_;
v_b_691_ = v___x_702_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_725_, lean_object* v_val_726_, lean_object* v_info_727_, lean_object* v___x_728_, lean_object* v_val_729_, lean_object* v___x_730_, lean_object* v_as_x27_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
uint8_t v___x_24203__boxed_735_; lean_object* v_res_736_; 
v___x_24203__boxed_735_ = lean_unbox(v___x_730_);
v_res_736_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_725_, v_val_726_, v_info_727_, v___x_728_, v_val_729_, v___x_24203__boxed_735_, v_as_x27_731_, v_b_732_, v___y_733_);
lean_dec(v___y_733_);
lean_dec_ref(v_info_727_);
lean_dec(v_val_726_);
lean_dec_ref(v_str_725_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_737_, v___y_739_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref(v___x_743_);
v___x_745_ = lean_whnf(v_a_744_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
return v___x_745_;
}
else
{
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_753_, lean_object* v___x_754_, lean_object* v_val_755_, lean_object* v___x_756_, lean_object* v_ci_757_, lean_object* v_info_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
if (lean_obj_tag(v_info_758_) == 1)
{
lean_object* v_i_763_; lean_object* v_expr_764_; 
v_i_763_ = lean_ctor_get(v_info_758_, 0);
v_expr_764_ = lean_ctor_get(v_i_763_, 3);
if (lean_obj_tag(v_expr_764_) == 1)
{
lean_object* v_lctx_765_; lean_object* v_expectedType_x3f_766_; uint8_t v_isBinder_767_; lean_object* v_fvarId_768_; lean_object* v___x_769_; 
v_lctx_765_ = lean_ctor_get(v_i_763_, 1);
v_expectedType_x3f_766_ = lean_ctor_get(v_i_763_, 2);
v_isBinder_767_ = lean_ctor_get_uint8(v_i_763_, sizeof(void*)*4);
v_fvarId_768_ = lean_ctor_get(v_expr_764_, 0);
v___x_769_ = l_Lean_Elab_Info_range_x3f(v_info_758_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_925_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_925_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_925_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_val_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_925_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_st_ref_get(v_val_753_);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_774_, v_val_770_);
lean_dec(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Lean_Elab_Info_stx(v_info_758_);
v___x_777_ = l_Lean_Syntax_getHeadInfo(v___x_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref(v___x_777_);
if (v_isBinder_767_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v___x_776_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
lean_ctor_set(v___x_772_, 0, v___x_754_);
v___x_779_ = v___x_772_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_754_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
else
{
lean_object* v___x_781_; 
lean_inc(v_fvarId_768_);
lean_inc_ref(v_lctx_765_);
v___x_781_ = lean_local_ctx_find(v_lctx_765_, v_fvarId_768_);
if (lean_obj_tag(v___x_781_) == 1)
{
lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_915_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_915_ == 0)
{
v___x_784_ = v___x_781_;
v_isShared_785_ = v_isSharedCheck_915_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v___x_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_915_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_start_786_; uint8_t v___x_787_; 
v_start_786_ = lean_ctor_get(v_val_770_, 0);
v___x_787_ = l_Lean_Syntax_Range_contains(v_val_755_, v_start_786_, v___x_775_);
if (v___x_787_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v_val_782_);
lean_dec(v___x_776_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 0);
lean_ctor_set(v___x_784_, 0, v___x_754_);
v___x_789_ = v___x_784_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_754_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
else
{
if (v___x_775_ == 0)
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = l_Lean_LocalDecl_userName(v_val_782_);
lean_dec(v_val_782_);
v___x_792_ = l_Lean_Name_hasMacroScopes(v___x_791_);
lean_dec(v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v_toCommandContextInfo_793_; lean_object* v_options_794_; lean_object* v___x_795_; 
v_toCommandContextInfo_793_ = lean_ctor_get(v_ci_757_, 0);
v_options_794_ = lean_ctor_get(v_toCommandContextInfo_793_, 4);
lean_inc_ref(v_options_794_);
v___x_795_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_794_, v___y_761_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_900_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_900_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_900_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_900_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
uint8_t v___x_800_; 
v___x_800_ = l_Lean_Linter_getLinterValue(v___x_756_, v_a_796_);
lean_dec(v_a_796_);
if (v___x_800_ == 0)
{
lean_object* v___x_802_; 
lean_del_object(v___x_784_);
lean_dec(v___x_776_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_754_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_754_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
else
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Syntax_getId(v___x_776_);
lean_dec(v___x_776_);
if (lean_obj_tag(v___x_804_) == 1)
{
lean_object* v_pre_805_; lean_object* v_str_806_; lean_object* v_ty_808_; lean_object* v___y_809_; lean_object* v___y_810_; 
v_pre_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_pre_805_);
v_str_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc_ref(v_str_806_);
if (lean_obj_tag(v_pre_805_) == 0)
{
lean_del_object(v___x_798_);
if (lean_obj_tag(v_expectedType_x3f_766_) == 1)
{
lean_object* v_val_867_; 
lean_del_object(v___x_772_);
v_val_867_ = lean_ctor_get(v_expectedType_x3f_766_, 0);
lean_inc(v_val_867_);
v_ty_808_ = v_val_867_;
v___y_809_ = v___y_760_;
v___y_810_ = v___y_761_;
goto v___jp_807_;
}
else
{
lean_object* v___x_868_; lean_object* v___x_869_; 
lean_inc_ref(v_expr_764_);
v___x_868_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_868_, 0, v_expr_764_);
lean_inc_ref(v_ci_757_);
lean_inc_ref(v_i_763_);
v___x_869_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_763_, v_ci_757_, v___x_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; 
lean_del_object(v___x_772_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v___x_869_);
v_ty_808_ = v_a_870_;
v___y_809_ = v___y_760_;
v___y_810_ = v___y_761_;
goto v___jp_807_;
}
else
{
lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_str_806_);
lean_dec_ref(v___x_804_);
lean_del_object(v___x_784_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
v_isSharedCheck_891_ = !lean_is_exclusive(v_val_770_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; lean_object* v_unused_893_; 
v_unused_892_ = lean_ctor_get(v_val_770_, 1);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_val_770_, 0);
lean_dec(v_unused_893_);
v___x_872_ = v_val_770_;
v_isShared_873_ = v_isSharedCheck_891_;
goto v_resetjp_871_;
}
else
{
lean_dec(v_val_770_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_891_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_890_; 
v_a_874_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_890_ == 0)
{
v___x_876_ = v___x_869_;
v_isShared_877_ = v_isSharedCheck_890_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_869_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_890_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_ref_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v_ref_878_ = lean_ctor_get(v___y_760_, 7);
v___x_879_ = lean_io_error_to_string(v_a_874_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 3);
lean_ctor_set(v___x_772_, 0, v___x_879_);
v___x_881_ = v___x_772_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_879_);
v___x_881_ = v_reuseFailAlloc_889_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_882_ = l_Lean_MessageData_ofFormat(v___x_881_);
lean_inc(v_ref_878_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___x_882_);
lean_ctor_set(v___x_872_, 0, v_ref_878_);
v___x_884_ = v___x_872_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_ref_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_884_);
v___x_886_ = v___x_876_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
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
}
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec_ref(v_str_806_);
lean_dec(v_pre_805_);
lean_dec_ref(v___x_804_);
lean_del_object(v___x_784_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_754_);
v___x_895_ = v___x_798_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_754_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
v___jp_807_:
{
lean_object* v___f_811_; lean_object* v___x_812_; 
v___f_811_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_811_, 0, v_ty_808_);
lean_inc_ref(v_i_763_);
v___x_812_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_763_, v_ci_757_, v___f_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_843_; 
lean_del_object(v___x_784_);
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_843_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_843_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_843_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Expr_getAppFn_x27(v_a_813_);
lean_dec(v_a_813_);
if (lean_obj_tag(v___x_817_) == 4)
{
lean_object* v_declName_818_; lean_object* v___x_819_; lean_object* v_env_820_; lean_object* v___x_821_; 
v_declName_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_declName_818_);
lean_dec_ref(v___x_817_);
v___x_819_ = lean_st_ref_get(v___y_810_);
v_env_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc_ref(v_env_820_);
lean_dec(v___x_819_);
v___x_821_ = l_Lean_Environment_find_x3f(v_env_820_, v_declName_818_, v___x_775_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_val_822_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v___x_821_);
if (lean_obj_tag(v_val_822_) == 5)
{
lean_object* v_val_823_; lean_object* v_ctors_824_; lean_object* v___x_825_; 
lean_del_object(v___x_815_);
v_val_823_ = lean_ctor_get(v_val_822_, 0);
lean_inc_ref(v_val_823_);
lean_dec_ref(v_val_822_);
v_ctors_824_ = lean_ctor_get(v_val_823_, 4);
lean_inc(v_ctors_824_);
lean_dec_ref(v_val_823_);
v___x_825_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_806_, v_val_753_, v_info_758_, v___x_804_, v_val_770_, v___x_775_, v_ctors_824_, v___x_754_, v___y_810_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_str_806_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v___x_825_, 0);
lean_dec(v_unused_833_);
v___x_827_ = v___x_825_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_dec(v___x_825_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_754_);
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_754_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
else
{
return v___x_825_;
}
}
else
{
lean_object* v___x_835_; 
lean_dec(v_val_822_);
lean_dec_ref(v_str_806_);
lean_dec_ref(v___x_804_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_754_);
v___x_835_ = v___x_815_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_754_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
else
{
lean_object* v___x_838_; 
lean_dec(v___x_821_);
lean_dec_ref(v_str_806_);
lean_dec_ref(v___x_804_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_754_);
v___x_838_ = v___x_815_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_754_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v___x_841_; 
lean_dec_ref(v___x_817_);
lean_dec_ref(v_str_806_);
lean_dec_ref(v___x_804_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_754_);
v___x_841_ = v___x_815_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_754_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_str_806_);
lean_dec_ref(v___x_804_);
lean_dec_ref(v_info_758_);
v_isSharedCheck_864_ = !lean_is_exclusive(v_val_770_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; lean_object* v_unused_866_; 
v_unused_865_ = lean_ctor_get(v_val_770_, 1);
lean_dec(v_unused_865_);
v_unused_866_ = lean_ctor_get(v_val_770_, 0);
lean_dec(v_unused_866_);
v___x_845_ = v_val_770_;
v_isShared_846_ = v_isSharedCheck_864_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_val_770_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_864_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_863_; 
v_a_847_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_863_ == 0)
{
v___x_849_ = v___x_812_;
v_isShared_850_ = v_isSharedCheck_863_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_812_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_863_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v_ref_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v_ref_851_ = lean_ctor_get(v___y_809_, 7);
v___x_852_ = lean_io_error_to_string(v_a_847_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 3);
lean_ctor_set(v___x_784_, 0, v___x_852_);
v___x_854_ = v___x_784_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_862_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = l_Lean_MessageData_ofFormat(v___x_854_);
lean_inc(v_ref_851_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 1, v___x_855_);
lean_ctor_set(v___x_845_, 0, v_ref_851_);
v___x_857_ = v___x_845_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_ref_851_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_857_);
v___x_859_ = v___x_849_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
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
lean_object* v___x_898_; 
lean_dec(v___x_804_);
lean_del_object(v___x_784_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_754_);
v___x_898_ = v___x_798_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_754_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_784_);
lean_dec(v___x_776_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
v_a_901_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_795_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_795_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v___x_910_; 
lean_dec(v___x_776_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 0);
lean_ctor_set(v___x_784_, 0, v___x_754_);
v___x_910_ = v___x_784_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_754_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
else
{
lean_object* v___x_913_; 
lean_dec(v_val_782_);
lean_dec(v___x_776_);
lean_del_object(v___x_772_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 0);
lean_ctor_set(v___x_784_, 0, v___x_754_);
v___x_913_ = v___x_784_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_754_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v___x_917_; 
lean_dec(v___x_781_);
lean_dec(v___x_776_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
lean_ctor_set(v___x_772_, 0, v___x_754_);
v___x_917_ = v___x_772_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_754_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v___x_777_);
lean_dec(v___x_776_);
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
lean_ctor_set(v___x_772_, 0, v___x_754_);
v___x_920_ = v___x_772_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_754_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec(v_val_770_);
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 0);
lean_ctor_set(v___x_772_, 0, v___x_754_);
v___x_923_ = v___x_772_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_754_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v___x_769_);
lean_dec_ref(v_ci_757_);
v_isSharedCheck_932_ = !lean_is_exclusive(v_info_758_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_info_758_, 0);
lean_dec(v_unused_933_);
v___x_927_ = v_info_758_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_dec(v_info_758_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 0);
lean_ctor_set(v___x_927_, 0, v___x_754_);
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_754_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v_ci_757_);
v_isSharedCheck_940_ = !lean_is_exclusive(v_info_758_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v_info_758_, 0);
lean_dec(v_unused_941_);
v___x_935_ = v_info_758_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_info_758_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 0);
lean_ctor_set(v___x_935_, 0, v___x_754_);
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_754_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v_info_758_);
lean_dec_ref(v_ci_757_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_754_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_943_, lean_object* v___x_944_, lean_object* v_val_945_, lean_object* v___x_946_, lean_object* v_ci_947_, lean_object* v_info_948_, lean_object* v_x_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_943_, v___x_944_, v_val_945_, v___x_946_, v_ci_947_, v_info_948_, v_x_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_x_949_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v_val_945_);
lean_dec(v_val_943_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_954_, lean_object* v_ci_955_, lean_object* v_i_956_, lean_object* v_cs_957_, lean_object* v_x_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_apply_6(v_postNode_954_, v_ci_955_, v_i_956_, v_cs_957_, v___y_959_, v___y_960_, lean_box(0));
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_963_, lean_object* v_ci_964_, lean_object* v_i_965_, lean_object* v_cs_966_, lean_object* v_x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_963_, v_ci_964_, v_i_965_, v_cs_966_, v_x_967_, v___y_968_, v___y_969_);
lean_dec(v_x_967_);
return v_res_971_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_toApplicative_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1012_; 
v___x_979_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_980_ = l_ReaderT_instMonad___redArg(v___x_979_);
v_toApplicative_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_980_, 1);
lean_dec(v_unused_1013_);
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1012_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_toApplicative_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1012_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_toFunctor_985_; lean_object* v_toSeq_986_; lean_object* v_toSeqLeft_987_; lean_object* v_toSeqRight_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1010_; 
v_toFunctor_985_ = lean_ctor_get(v_toApplicative_981_, 0);
v_toSeq_986_ = lean_ctor_get(v_toApplicative_981_, 2);
v_toSeqLeft_987_ = lean_ctor_get(v_toApplicative_981_, 3);
v_toSeqRight_988_ = lean_ctor_get(v_toApplicative_981_, 4);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_toApplicative_981_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; 
v_unused_1011_ = lean_ctor_get(v_toApplicative_981_, 1);
lean_dec(v_unused_1011_);
v___x_990_ = v_toApplicative_981_;
v_isShared_991_ = v_isSharedCheck_1010_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_toSeqRight_988_);
lean_inc(v_toSeqLeft_987_);
lean_inc(v_toSeq_986_);
lean_inc(v_toFunctor_985_);
lean_dec(v_toApplicative_981_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1010_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___f_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_1001_; 
v___f_992_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_993_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_985_);
v___f_994_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_994_, 0, v_toFunctor_985_);
v___f_995_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_995_, 0, v_toFunctor_985_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___f_994_);
lean_ctor_set(v___x_996_, 1, v___f_995_);
v___f_997_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_997_, 0, v_toSeqRight_988_);
v___f_998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_998_, 0, v_toSeqLeft_987_);
v___f_999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_999_, 0, v_toSeq_986_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 4, v___f_997_);
lean_ctor_set(v___x_990_, 3, v___f_998_);
lean_ctor_set(v___x_990_, 2, v___f_999_);
lean_ctor_set(v___x_990_, 1, v___f_992_);
lean_ctor_set(v___x_990_, 0, v___x_996_);
v___x_1001_ = v___x_990_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v___f_992_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v___f_999_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v___f_998_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v___f_997_);
v___x_1001_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___f_993_);
lean_ctor_set(v___x_983_, 0, v___x_1001_);
v___x_1003_ = v___x_983_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___f_993_);
v___x_1003_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_20526__overap_1006_; lean_object* v___x_1007_; 
v___x_1004_ = lean_box(0);
v___x_1005_ = l_instInhabitedOfMonad___redArg(v___x_1003_, v___x_1004_);
v___x_20526__overap_1006_ = lean_panic_fn(v___x_1005_, v_msg_975_);
v___x_1007_ = lean_apply_3(v___x_20526__overap_1006_, v___y_976_, v___y_977_, lean_box(0));
return v___x_1007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1014_, v___y_1015_, v___y_1016_);
return v_res_1018_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1022_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1023_ = lean_unsigned_to_nat(21u);
v___x_1024_ = lean_unsigned_to_nat(65u);
v___x_1025_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1026_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1027_ = l_mkPanicMessageWithDecl(v___x_1026_, v___x_1025_, v___x_1024_, v___x_1023_, v___x_1022_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1028_, lean_object* v_postNode_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
switch(lean_obj_tag(v_x_1031_))
{
case 0:
{
lean_object* v_i_1035_; lean_object* v_t_1036_; lean_object* v___x_1037_; 
v_i_1035_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_i_1035_);
v_t_1036_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_t_1036_);
lean_dec_ref(v_x_1031_);
v___x_1037_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1035_, v_x_1030_);
v_x_1030_ = v___x_1037_;
v_x_1031_ = v_t_1036_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref(v_x_1031_);
lean_dec_ref(v_postNode_1029_);
lean_dec_ref(v_preNode_1028_);
v___x_1039_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1040_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1039_, v___y_1032_, v___y_1033_);
return v___x_1040_;
}
else
{
lean_object* v_i_1041_; lean_object* v_children_1042_; lean_object* v_val_1043_; lean_object* v___x_1044_; 
v_i_1041_ = lean_ctor_get(v_x_1031_, 0);
lean_inc_ref(v_i_1041_);
v_children_1042_ = lean_ctor_get(v_x_1031_, 1);
lean_inc_ref(v_children_1042_);
lean_dec_ref(v_x_1031_);
v_val_1043_ = lean_ctor_get(v_x_1030_, 0);
lean_inc(v_val_1043_);
lean_inc_ref(v_preNode_1028_);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc_ref(v_children_1042_);
lean_inc_ref(v_i_1041_);
lean_inc(v_val_1043_);
v___x_1044_ = lean_apply_6(v_preNode_1028_, v_val_1043_, v_i_1041_, v_children_1042_, v___y_1032_, v___y_1033_, lean_box(0));
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; uint8_t v___x_1046_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_a_1045_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = lean_unbox(v_a_1045_);
lean_dec(v_a_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_preNode_1028_);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_x_1030_, 0);
lean_dec(v_unused_1072_);
v___x_1048_ = v_x_1030_;
v_isShared_1049_ = v_isSharedCheck_1071_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_x_1030_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1071_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_apply_7(v_postNode_1029_, v_val_1043_, v_i_1041_, v_children_1042_, v___x_1050_, v___y_1032_, v___y_1033_, lean_box(0));
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1062_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1062_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1062_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_a_1052_);
v___x_1057_ = v___x_1048_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_del_object(v___x_1048_);
v_a_1063_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1051_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1051_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1073_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1030_, v_i_1041_);
v___x_1074_ = l_Lean_PersistentArray_toList___redArg(v_children_1042_);
v___x_1075_ = lean_box(0);
lean_inc(v___y_1033_);
lean_inc_ref(v___y_1032_);
lean_inc_ref(v_postNode_1029_);
v___x_1076_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1028_, v_postNode_1029_, v___x_1073_, v___x_1074_, v___x_1075_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_apply_7(v_postNode_1029_, v_val_1043_, v_i_1041_, v_children_1042_, v_a_1077_, v___y_1032_, v___y_1033_, lean_box(0));
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v_a_1079_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1078_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1078_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_val_1043_);
lean_dec_ref(v_children_1042_);
lean_dec_ref(v_i_1041_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_postNode_1029_);
v_a_1096_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1076_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1076_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_val_1043_);
lean_dec_ref(v_children_1042_);
lean_dec_ref(v_x_1030_);
lean_dec_ref(v_i_1041_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_postNode_1029_);
lean_dec_ref(v_preNode_1028_);
v_a_1104_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1044_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1044_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
default: 
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v_x_1030_);
lean_dec_ref(v_postNode_1029_);
lean_dec_ref(v_preNode_1028_);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_x_1031_, 0);
lean_dec(v_unused_1120_);
v___x_1113_ = v_x_1031_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v_x_1031_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1115_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1121_, lean_object* v_postNode_1122_, lean_object* v___x_1123_, lean_object* v_x_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
if (lean_obj_tag(v_x_1124_) == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___x_1123_);
lean_dec_ref(v_postNode_1122_);
lean_dec_ref(v_preNode_1121_);
v___x_1129_ = l_List_reverse___redArg(v_x_1125_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
else
{
lean_object* v_head_1131_; lean_object* v_tail_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1150_; 
v_head_1131_ = lean_ctor_get(v_x_1124_, 0);
v_tail_1132_ = lean_ctor_get(v_x_1124_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_x_1124_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1134_ = v_x_1124_;
v_isShared_1135_ = v_isSharedCheck_1150_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_tail_1132_);
lean_inc(v_head_1131_);
lean_dec(v_x_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1150_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; 
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v___x_1123_);
lean_inc_ref(v_postNode_1122_);
lean_inc_ref(v_preNode_1121_);
v___x_1136_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1121_, v_postNode_1122_, v___x_1123_, v_head_1131_, v___y_1126_, v___y_1127_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v_x_1125_);
lean_ctor_set(v___x_1134_, 0, v_a_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1137_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_x_1125_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
v_x_1124_ = v_tail_1132_;
v_x_1125_ = v___x_1139_;
goto _start;
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_del_object(v___x_1134_);
lean_dec(v_tail_1132_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v_x_1125_);
lean_dec(v___x_1123_);
lean_dec_ref(v_postNode_1122_);
lean_dec_ref(v_preNode_1121_);
v_a_1142_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1136_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1136_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1151_, lean_object* v_postNode_1152_, lean_object* v___x_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1151_, v_postNode_1152_, v___x_1153_, v_x_1154_, v_x_1155_, v___y_1156_, v___y_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1160_, lean_object* v_postNode_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1160_, v_postNode_1161_, v_x_1162_, v_x_1163_, v___y_1164_, v___y_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1168_, lean_object* v_postNode_1169_, lean_object* v_ctx_x3f_1170_, lean_object* v_t_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1175_, 0, v_postNode_1169_);
v___x_1176_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1168_, v___f_1175_, v_ctx_x3f_1170_, v_t_1171_, v___y_1172_, v___y_1173_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1184_; 
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v___x_1176_, 0);
lean_dec(v_unused_1185_);
v___x_1178_ = v___x_1176_;
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v___x_1176_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_box(0);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1176_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1176_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1194_, lean_object* v_postNode_1195_, lean_object* v_ctx_x3f_1196_, lean_object* v_t_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1194_, v_postNode_1195_, v_ctx_x3f_1196_, v_t_1197_, v___y_1198_, v___y_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1202_, lean_object* v_val_1203_, lean_object* v_val_1204_, lean_object* v_as_1205_, size_t v_sz_1206_, size_t v_i_1207_, lean_object* v_b_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1207_, v_sz_1206_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_val_1204_);
lean_dec(v_val_1203_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_b_1208_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___f_1218_; lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1214_ = lean_box(v___x_1202_);
v___f_1215_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1215_, 0, v___x_1214_);
v___x_1216_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1217_ = lean_box(0);
lean_inc_ref(v_val_1204_);
lean_inc(v_val_1203_);
v___f_1218_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1218_, 0, v_val_1203_);
lean_closure_set(v___f_1218_, 1, v___x_1217_);
lean_closure_set(v___f_1218_, 2, v_val_1204_);
lean_closure_set(v___f_1218_, 3, v___x_1216_);
v_a_1219_ = lean_array_uget_borrowed(v_as_1205_, v_i_1207_);
v___x_1220_ = lean_box(0);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
lean_inc(v_a_1219_);
v___x_1221_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1215_, v___f_1218_, v___x_1220_, v_a_1219_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1221_) == 0)
{
size_t v___x_1222_; size_t v___x_1223_; 
lean_dec_ref(v___x_1221_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1207_, v___x_1222_);
v_i_1207_ = v___x_1223_;
v_b_1208_ = v___x_1217_;
goto _start;
}
else
{
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec_ref(v_val_1204_);
lean_dec(v_val_1203_);
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1225_, lean_object* v_val_1226_, lean_object* v_val_1227_, lean_object* v_as_1228_, lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_b_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
uint8_t v___x_25079__boxed_1235_; size_t v_sz_boxed_1236_; size_t v_i_boxed_1237_; lean_object* v_res_1238_; 
v___x_25079__boxed_1235_ = lean_unbox(v___x_1225_);
v_sz_boxed_1236_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1237_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_25079__boxed_1235_, v_val_1226_, v_val_1227_, v_as_1228_, v_sz_boxed_1236_, v_i_boxed_1237_, v_b_1231_, v___y_1232_, v___y_1233_);
lean_dec_ref(v_as_1228_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
if (lean_obj_tag(v_x_1240_) == 0)
{
return v_x_1239_;
}
else
{
lean_object* v_key_1241_; lean_object* v_value_1242_; lean_object* v_tail_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_key_1241_ = lean_ctor_get(v_x_1240_, 0);
v_value_1242_ = lean_ctor_get(v_x_1240_, 1);
v_tail_1243_ = lean_ctor_get(v_x_1240_, 2);
lean_inc(v_value_1242_);
lean_inc(v_key_1241_);
v___x_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_key_1241_);
lean_ctor_set(v___x_1244_, 1, v_value_1242_);
v___x_1245_ = lean_array_push(v_x_1239_, v___x_1244_);
v_x_1239_ = v___x_1245_;
v_x_1240_ = v_tail_1243_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1247_, v_x_1248_);
lean_dec(v_x_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1250_, size_t v_i_1251_, size_t v_stop_1252_, lean_object* v_b_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_eq(v_i_1251_, v_stop_1252_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; 
v___x_1255_ = lean_array_uget_borrowed(v_as_1250_, v_i_1251_);
v___x_1256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1253_, v___x_1255_);
v___x_1257_ = ((size_t)1ULL);
v___x_1258_ = lean_usize_add(v_i_1251_, v___x_1257_);
v_i_1251_ = v___x_1258_;
v_b_1253_ = v___x_1256_;
goto _start;
}
else
{
return v_b_1253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1260_, lean_object* v_i_1261_, lean_object* v_stop_1262_, lean_object* v_b_1263_){
_start:
{
size_t v_i_boxed_1264_; size_t v_stop_boxed_1265_; lean_object* v_res_1266_; 
v_i_boxed_1264_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_stop_boxed_1265_ = lean_unbox_usize(v_stop_1262_);
lean_dec(v_stop_1262_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1260_, v_i_boxed_1264_, v_stop_boxed_1265_, v_b_1263_);
lean_dec_ref(v_as_1260_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v_scopes_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_opts_1274_; lean_object* v___x_1275_; 
v___x_1270_ = lean_st_ref_get(v___y_1268_);
v_scopes_1271_ = lean_ctor_get(v___x_1270_, 2);
lean_inc(v_scopes_1271_);
lean_dec(v___x_1270_);
v___x_1272_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1273_ = l_List_head_x21___redArg(v___x_1272_, v_scopes_1271_);
lean_dec(v_scopes_1271_);
v_opts_1274_ = lean_ctor_get(v___x_1273_, 1);
lean_inc_ref(v_opts_1274_);
lean_dec(v___x_1273_);
v___x_1275_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1274_, v___y_1268_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1279_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_unsigned_to_nat(16u);
v___x_1282_ = lean_mk_array(v___x_1281_, v___x_1280_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
lean_ctor_set(v___x_1285_, 1, v___x_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1361_; 
v___x_1290_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1287_, v___y_1288_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1293_ = v___x_1290_;
v_isShared_1294_ = v_isSharedCheck_1361_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1361_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1296_ = l_Lean_Linter_getLinterValue(v___x_1295_, v_a_1291_);
lean_dec(v_a_1291_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
v___x_1297_ = lean_box(0);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1297_);
v___x_1299_ = v___x_1293_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
else
{
uint8_t v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = 0;
v___x_1302_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1286_, v___x_1301_);
if (lean_obj_tag(v___x_1302_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_infoState_1308_; lean_object* v_trees_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; size_t v_sz_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
lean_del_object(v___x_1293_);
v_val_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = lean_st_ref_get(v___y_1288_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1307_ = lean_st_mk_ref(v___x_1306_);
v_infoState_1308_ = lean_ctor_get(v___x_1304_, 8);
lean_inc_ref(v_infoState_1308_);
lean_dec(v___x_1304_);
v_trees_1309_ = lean_ctor_get(v_infoState_1308_, 2);
lean_inc_ref(v_trees_1309_);
lean_dec_ref(v_infoState_1308_);
v___x_1310_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1309_);
lean_dec_ref(v_trees_1309_);
v___x_1311_ = lean_box(0);
v_sz_1312_ = lean_array_size(v___x_1310_);
v___x_1313_ = ((size_t)0ULL);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___x_1307_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1296_, v___x_1307_, v_val_1303_, v___x_1310_, v_sz_1312_, v___x_1313_, v___x_1311_, v___y_1287_, v___y_1288_);
lean_dec_ref(v___x_1310_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; lean_object* v___y_1317_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1341_; lean_object* v_size_1347_; lean_object* v_buckets_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
lean_dec_ref(v___x_1314_);
v___x_1315_ = lean_st_ref_get(v___x_1307_);
lean_dec(v___x_1307_);
v_size_1347_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_size_1347_);
v_buckets_1348_ = lean_ctor_get(v___x_1315_, 1);
lean_inc_ref(v_buckets_1348_);
lean_dec(v___x_1315_);
v___x_1349_ = lean_mk_empty_array_with_capacity(v_size_1347_);
lean_dec(v_size_1347_);
v___x_1350_ = lean_array_get_size(v_buckets_1348_);
v___x_1351_ = lean_nat_dec_lt(v___x_1305_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_dec_ref(v_buckets_1348_);
v___y_1341_ = v___x_1349_;
goto v___jp_1340_;
}
else
{
uint8_t v___x_1352_; 
v___x_1352_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1352_ == 0)
{
if (v___x_1351_ == 0)
{
lean_dec_ref(v_buckets_1348_);
v___y_1341_ = v___x_1349_;
goto v___jp_1340_;
}
else
{
size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_usize_of_nat(v___x_1350_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1348_, v___x_1313_, v___x_1353_, v___x_1349_);
lean_dec_ref(v_buckets_1348_);
v___y_1341_ = v___x_1354_;
goto v___jp_1340_;
}
}
else
{
size_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_usize_of_nat(v___x_1350_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1348_, v___x_1313_, v___x_1355_, v___x_1349_);
lean_dec_ref(v_buckets_1348_);
v___y_1341_ = v___x_1356_;
goto v___jp_1340_;
}
}
v___jp_1316_:
{
size_t v_sz_1318_; lean_object* v___x_1319_; 
v_sz_1318_ = lean_array_size(v___y_1317_);
v___x_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1317_, v_sz_1318_, v___x_1313_, v___x_1311_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1317_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1319_, 0);
lean_dec(v_unused_1327_);
v___x_1321_ = v___x_1319_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_dec(v___x_1319_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1311_);
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1311_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
else
{
return v___x_1319_;
}
}
v___jp_1328_:
{
lean_object* v___x_1333_; 
lean_dec(v___y_1330_);
v___x_1333_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1331_, v___y_1329_, v___y_1332_);
lean_dec(v___y_1332_);
v___y_1317_ = v___x_1333_;
goto v___jp_1316_;
}
v___jp_1334_:
{
uint8_t v___x_1339_; 
v___x_1339_ = lean_nat_dec_le(v___y_1338_, v___y_1335_);
if (v___x_1339_ == 0)
{
lean_dec(v___y_1335_);
lean_inc(v___y_1338_);
v___y_1329_ = v___y_1338_;
v___y_1330_ = v___y_1336_;
v___y_1331_ = v___y_1337_;
v___y_1332_ = v___y_1338_;
goto v___jp_1328_;
}
else
{
v___y_1329_ = v___y_1338_;
v___y_1330_ = v___y_1336_;
v___y_1331_ = v___y_1337_;
v___y_1332_ = v___y_1335_;
goto v___jp_1328_;
}
}
v___jp_1340_:
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = lean_array_get_size(v___y_1341_);
v___x_1343_ = lean_nat_dec_eq(v___x_1342_, v___x_1305_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = lean_unsigned_to_nat(1u);
v___x_1345_ = lean_nat_sub(v___x_1342_, v___x_1344_);
v___x_1346_ = lean_nat_dec_le(v___x_1305_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_inc(v___x_1345_);
v___y_1335_ = v___x_1345_;
v___y_1336_ = v___x_1342_;
v___y_1337_ = v___y_1341_;
v___y_1338_ = v___x_1345_;
goto v___jp_1334_;
}
else
{
v___y_1335_ = v___x_1345_;
v___y_1336_ = v___x_1342_;
v___y_1337_ = v___y_1341_;
v___y_1338_ = v___x_1305_;
goto v___jp_1334_;
}
}
else
{
v___y_1317_ = v___y_1341_;
goto v___jp_1316_;
}
}
}
else
{
lean_dec(v___x_1307_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v___x_1314_;
}
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_dec(v___x_1302_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
v___x_1357_ = lean_box(0);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1357_);
v___x_1359_ = v___x_1293_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1362_, v___y_1363_, v___y_1364_);
lean_dec(v_cmdStx_1362_);
return v_res_1366_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1376_, lean_object* v_m_1377_, lean_object* v_a_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1377_, v_a_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1380_, lean_object* v_m_1381_, lean_object* v_a_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1380_, v_m_1381_, v_a_1382_);
lean_dec_ref(v_a_1382_);
lean_dec_ref(v_m_1381_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1385_, lean_object* v_m_1386_, lean_object* v_a_1387_, lean_object* v_b_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1386_, v_a_1387_, v_b_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1390_, lean_object* v_val_1391_, lean_object* v_info_1392_, lean_object* v___x_1393_, lean_object* v_val_1394_, uint8_t v___x_1395_, lean_object* v_as_1396_, lean_object* v_as_x27_1397_, lean_object* v_b_1398_, lean_object* v_a_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1390_, v_val_1391_, v_info_1392_, v___x_1393_, v_val_1394_, v___x_1395_, v_as_x27_1397_, v_b_1398_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1404_, lean_object* v_val_1405_, lean_object* v_info_1406_, lean_object* v___x_1407_, lean_object* v_val_1408_, lean_object* v___x_1409_, lean_object* v_as_1410_, lean_object* v_as_x27_1411_, lean_object* v_b_1412_, lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_25371__boxed_1417_; lean_object* v_res_1418_; 
v___x_25371__boxed_1417_ = lean_unbox(v___x_1409_);
v_res_1418_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1404_, v_val_1405_, v_info_1406_, v___x_1407_, v_val_1408_, v___x_25371__boxed_1417_, v_as_1410_, v_as_x27_1411_, v_b_1412_, v_a_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v_as_1410_);
lean_dec_ref(v_info_1406_);
lean_dec(v_val_1405_);
lean_dec_ref(v_str_1404_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1419_, lean_object* v_as_1420_, lean_object* v_lo_1421_, lean_object* v_hi_1422_, lean_object* v_w_1423_, lean_object* v_hlo_1424_, lean_object* v_hhi_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_as_1420_, v_lo_1421_, v_hi_1422_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1427_, lean_object* v_as_1428_, lean_object* v_lo_1429_, lean_object* v_hi_1430_, lean_object* v_w_1431_, lean_object* v_hlo_1432_, lean_object* v_hhi_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1427_, v_as_1428_, v_lo_1429_, v_hi_1430_, v_w_1431_, v_hlo_1432_, v_hhi_1433_);
lean_dec(v_hi_1430_);
lean_dec(v_n_1427_);
return v_res_1434_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1435_, lean_object* v_a_1436_, lean_object* v_x_1437_){
_start:
{
uint8_t v___x_1438_; 
v___x_1438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1436_, v_x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1439_, lean_object* v_a_1440_, lean_object* v_x_1441_){
_start:
{
uint8_t v_res_1442_; lean_object* v_r_1443_; 
v_res_1442_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1439_, v_a_1440_, v_x_1441_);
lean_dec(v_x_1441_);
lean_dec_ref(v_a_1440_);
v_r_1443_ = lean_box(v_res_1442_);
return v_r_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1444_, lean_object* v_data_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1447_, lean_object* v_a_1448_, lean_object* v_b_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1448_, v_b_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1452_, lean_object* v_msg_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1453_, v___y_1454_, v___y_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1458_, v_msg_1459_, v___y_1460_, v___y_1461_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1464_, lean_object* v_preNode_1465_, lean_object* v_postNode_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1465_, v_postNode_1466_, v_x_1467_, v_x_1468_, v___y_1469_, v___y_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1473_, lean_object* v_preNode_1474_, lean_object* v_postNode_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1473_, v_preNode_1474_, v_postNode_1475_, v_x_1476_, v_x_1477_, v___y_1478_, v___y_1479_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1482_, lean_object* v_i_1483_, lean_object* v_source_1484_, lean_object* v_target_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1483_, v_source_1484_, v_target_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1487_, lean_object* v_preNode_1488_, lean_object* v_postNode_1489_, lean_object* v___x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1488_, v_postNode_1489_, v___x_1490_, v_x_1491_, v_x_1492_, v___y_1493_, v___y_1494_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1497_, lean_object* v_preNode_1498_, lean_object* v_postNode_1499_, lean_object* v___x_1500_, lean_object* v_x_1501_, lean_object* v_x_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1497_, v_preNode_1498_, v_postNode_1499_, v___x_1500_, v_x_1501_, v_x_1502_, v___y_1503_, v___y_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1507_, v___y_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1518_, v_x_1519_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1523_ = l_Lean_Elab_Command_addLinter(v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1525_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_ConstructorAsVariable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_constructorNameAsVariable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_constructorNameAsVariable);
lean_dec_ref(res);
res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_ConstructorAsVariable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_ConstructorAsVariable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_ConstructorAsVariable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_ConstructorAsVariable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_ConstructorAsVariable(builtin);
}
#ifdef __cplusplus
}
#endif
