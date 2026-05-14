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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "constructorNameAsVariable"};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 93, 54, 211, 83, 91, 108, 28)}};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "enable the linter that warns when bound variable names are nullary constructor names"};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 65, 101, 89, 237, 205, 227, 46)}};
static const lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_constructorNameAsVariable;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 75, 81, 128, 80, 183, 232, 251)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(lean_object* v_o_59_, lean_object* v___y_60_){
_start:
{
lean_object* v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_toEnvExtension_65_; lean_object* v_asyncMode_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_linterSets_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v_env_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_env_63_);
lean_dec(v___x_62_);
v___x_64_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_65_ = lean_ctor_get(v___x_64_, 0);
v_asyncMode_66_ = lean_ctor_get(v_toEnvExtension_65_, 2);
v___x_67_ = lean_box(1);
v___x_68_ = lean_box(0);
v_linterSets_69_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_67_, v___x_64_, v_env_63_, v_asyncMode_66_, v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_o_59_);
lean_ctor_set(v___x_70_, 1, v_linterSets_69_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(lean_object* v_o_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_72_, v___y_73_);
lean_dec(v___y_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object* v_o_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_76_, v___y_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(lean_object* v_o_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(v_o_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object* v_e_86_, lean_object* v___y_87_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_Expr_hasMVar(v_e_86_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v_e_86_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_mctx_92_; lean_object* v___x_93_; lean_object* v_fst_94_; lean_object* v_snd_95_; lean_object* v___x_96_; lean_object* v_cache_97_; lean_object* v_zetaDeltaFVarIds_98_; lean_object* v_postponed_99_; lean_object* v_diag_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_109_; 
v___x_91_ = lean_st_ref_get(v___y_87_);
v_mctx_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_mctx_92_);
lean_dec(v___x_91_);
v___x_93_ = l_Lean_instantiateMVarsCore(v_mctx_92_, v_e_86_);
v_fst_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_fst_94_);
v_snd_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_snd_95_);
lean_dec_ref(v___x_93_);
v___x_96_ = lean_st_ref_take(v___y_87_);
v_cache_97_ = lean_ctor_get(v___x_96_, 1);
v_zetaDeltaFVarIds_98_ = lean_ctor_get(v___x_96_, 2);
v_postponed_99_ = lean_ctor_get(v___x_96_, 3);
v_diag_100_ = lean_ctor_get(v___x_96_, 4);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v___x_96_, 0);
lean_dec(v_unused_110_);
v___x_102_ = v___x_96_;
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_diag_100_);
lean_inc(v_postponed_99_);
lean_inc(v_zetaDeltaFVarIds_98_);
lean_inc(v_cache_97_);
lean_dec(v___x_96_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_109_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_snd_95_);
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_snd_95_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_cache_97_);
lean_ctor_set(v_reuseFailAlloc_108_, 2, v_zetaDeltaFVarIds_98_);
lean_ctor_set(v_reuseFailAlloc_108_, 3, v_postponed_99_);
lean_ctor_set(v_reuseFailAlloc_108_, 4, v_diag_100_);
v___x_105_ = v_reuseFailAlloc_108_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_st_ref_set(v___y_87_, v___x_105_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v_fst_94_);
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object* v_e_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_e_111_, v___y_112_);
lean_dec(v___y_112_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object* v_e_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_e_115_, v___y_117_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object* v_e_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(v_e_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(lean_object* v_hi_129_, lean_object* v_pivot_130_, lean_object* v_as_131_, lean_object* v_i_132_, lean_object* v_k_133_){
_start:
{
uint8_t v___x_134_; 
v___x_134_ = lean_nat_dec_lt(v_k_133_, v_hi_129_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; 
lean_dec(v_k_133_);
v___x_135_ = lean_array_fswap(v_as_131_, v_i_132_, v_hi_129_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_i_132_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
return v___x_136_;
}
else
{
lean_object* v___x_137_; lean_object* v_fst_138_; lean_object* v_fst_139_; lean_object* v_start_140_; lean_object* v_start_141_; uint8_t v___x_142_; 
v___x_137_ = lean_array_fget_borrowed(v_as_131_, v_k_133_);
v_fst_138_ = lean_ctor_get(v___x_137_, 0);
v_fst_139_ = lean_ctor_get(v_pivot_130_, 0);
v_start_140_ = lean_ctor_get(v_fst_138_, 0);
v_start_141_ = lean_ctor_get(v_fst_139_, 0);
v___x_142_ = lean_nat_dec_lt(v_start_140_, v_start_141_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_add(v_k_133_, v___x_143_);
lean_dec(v_k_133_);
v_k_133_ = v___x_144_;
goto _start;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_array_fswap(v_as_131_, v_i_132_, v_k_133_);
v___x_147_ = lean_unsigned_to_nat(1u);
v___x_148_ = lean_nat_add(v_i_132_, v___x_147_);
lean_dec(v_i_132_);
v___x_149_ = lean_nat_add(v_k_133_, v___x_147_);
lean_dec(v_k_133_);
v_as_131_ = v___x_146_;
v_i_132_ = v___x_148_;
v_k_133_ = v___x_149_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg___boxed(lean_object* v_hi_151_, lean_object* v_pivot_152_, lean_object* v_as_153_, lean_object* v_i_154_, lean_object* v_k_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_151_, v_pivot_152_, v_as_153_, v_i_154_, v_k_155_);
lean_dec_ref(v_pivot_152_);
lean_dec(v_hi_151_);
return v_res_156_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(lean_object* v_x1_157_, lean_object* v_x2_158_){
_start:
{
lean_object* v_fst_159_; lean_object* v_fst_160_; lean_object* v_start_161_; lean_object* v_start_162_; uint8_t v___x_163_; 
v_fst_159_ = lean_ctor_get(v_x1_157_, 0);
v_fst_160_ = lean_ctor_get(v_x2_158_, 0);
v_start_161_ = lean_ctor_get(v_fst_159_, 0);
v_start_162_ = lean_ctor_get(v_fst_160_, 0);
v___x_163_ = lean_nat_dec_lt(v_start_161_, v_start_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(lean_object* v_x1_164_, lean_object* v_x2_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v_x1_164_, v_x2_165_);
lean_dec_ref(v_x2_165_);
lean_dec_ref(v_x1_164_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(lean_object* v_n_168_, lean_object* v_as_169_, lean_object* v_lo_170_, lean_object* v_hi_171_){
_start:
{
lean_object* v___y_173_; uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_lt(v_lo_170_, v_hi_171_);
if (v___x_183_ == 0)
{
lean_dec(v_lo_170_);
return v_as_169_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_mid_186_; lean_object* v___y_188_; lean_object* v___y_194_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_184_ = lean_nat_add(v_lo_170_, v_hi_171_);
v___x_185_ = lean_unsigned_to_nat(1u);
v_mid_186_ = lean_nat_shiftr(v___x_184_, v___x_185_);
lean_dec(v___x_184_);
v___x_199_ = lean_array_fget_borrowed(v_as_169_, v_mid_186_);
v___x_200_ = lean_array_fget_borrowed(v_as_169_, v_lo_170_);
v___x_201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
v___y_194_ = v_as_169_;
goto v___jp_193_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_fswap(v_as_169_, v_lo_170_, v_mid_186_);
v___y_194_ = v___x_202_;
goto v___jp_193_;
}
v___jp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_189_ = lean_array_fget_borrowed(v___y_188_, v_mid_186_);
v___x_190_ = lean_array_fget_borrowed(v___y_188_, v_hi_171_);
v___x_191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v_mid_186_);
v___y_173_ = v___y_188_;
goto v___jp_172_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_array_fswap(v___y_188_, v_mid_186_, v_hi_171_);
lean_dec(v_mid_186_);
v___y_173_ = v___x_192_;
goto v___jp_172_;
}
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = lean_array_fget_borrowed(v___y_194_, v_hi_171_);
v___x_196_ = lean_array_fget_borrowed(v___y_194_, v_lo_170_);
v___x_197_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_195_, v___x_196_);
if (v___x_197_ == 0)
{
v___y_188_ = v___y_194_;
goto v___jp_187_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_array_fswap(v___y_194_, v_lo_170_, v_hi_171_);
v___y_188_ = v___x_198_;
goto v___jp_187_;
}
}
}
v___jp_172_:
{
lean_object* v_pivot_174_; lean_object* v___x_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; uint8_t v___x_178_; 
v_pivot_174_ = lean_array_fget(v___y_173_, v_hi_171_);
lean_inc_n(v_lo_170_, 2);
v___x_175_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_171_, v_pivot_174_, v___y_173_, v_lo_170_, v_lo_170_);
lean_dec(v_pivot_174_);
v_fst_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v___x_175_);
v___x_178_ = lean_nat_dec_le(v_hi_171_, v_fst_176_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_168_, v_snd_177_, v_lo_170_, v_fst_176_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_fst_176_, v___x_180_);
lean_dec(v_fst_176_);
v_as_169_ = v___x_179_;
v_lo_170_ = v___x_181_;
goto _start;
}
else
{
lean_dec(v_fst_176_);
lean_dec(v_lo_170_);
return v_snd_177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(lean_object* v_n_203_, lean_object* v_as_204_, lean_object* v_lo_205_, lean_object* v_hi_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_203_, v_as_204_, v_lo_205_, v_hi_206_);
lean_dec(v_hi_206_);
lean_dec(v_n_203_);
return v_res_207_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(uint8_t v___y_209_, uint8_t v_suppressElabErrors_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_211_) == 1)
{
lean_object* v_pre_212_; 
v_pre_212_ = lean_ctor_get(v_x_211_, 0);
if (lean_obj_tag(v_pre_212_) == 0)
{
lean_object* v_str_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_str_213_ = lean_ctor_get(v_x_211_, 1);
v___x_214_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0));
v___x_215_ = lean_string_dec_eq(v_str_213_, v___x_214_);
if (v___x_215_ == 0)
{
return v___y_209_;
}
else
{
return v_suppressElabErrors_210_;
}
}
else
{
return v___y_209_;
}
}
else
{
return v___y_209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed(lean_object* v___y_216_, lean_object* v_suppressElabErrors_217_, lean_object* v_x_218_){
_start:
{
uint8_t v___y_21703__boxed_219_; uint8_t v_suppressElabErrors_boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___y_21703__boxed_219_ = lean_unbox(v___y_216_);
v_suppressElabErrors_boxed_220_ = lean_unbox(v_suppressElabErrors_217_);
v_res_221_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21703__boxed_219_, v_suppressElabErrors_boxed_220_, v_x_218_);
lean_dec(v_x_218_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(lean_object* v_opts_223_, lean_object* v_opt_224_){
_start:
{
lean_object* v_name_225_; lean_object* v_defValue_226_; lean_object* v_map_227_; lean_object* v___x_228_; 
v_name_225_ = lean_ctor_get(v_opt_224_, 0);
v_defValue_226_ = lean_ctor_get(v_opt_224_, 1);
v_map_227_ = lean_ctor_get(v_opts_223_, 0);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_227_, v_name_225_);
if (lean_obj_tag(v___x_228_) == 0)
{
uint8_t v___x_229_; 
v___x_229_ = lean_unbox(v_defValue_226_);
return v___x_229_;
}
else
{
lean_object* v_val_230_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref(v___x_228_);
if (lean_obj_tag(v_val_230_) == 1)
{
uint8_t v_v_231_; 
v_v_231_ = lean_ctor_get_uint8(v_val_230_, 0);
lean_dec_ref(v_val_230_);
return v_v_231_;
}
else
{
uint8_t v___x_232_; 
lean_dec(v_val_230_);
v___x_232_ = lean_unbox(v_defValue_226_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(lean_object* v_opts_233_, lean_object* v_opt_234_){
_start:
{
uint8_t v_res_235_; lean_object* v_r_236_; 
v_res_235_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_233_, v_opt_234_);
lean_dec_ref(v_opt_234_);
lean_dec_ref(v_opts_233_);
v_r_236_ = lean_box(v_res_235_);
return v_r_236_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_237_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
lean_ctor_set(v___x_242_, 2, v___x_241_);
lean_ctor_set(v___x_242_, 3, v___x_241_);
lean_ctor_set(v___x_242_, 4, v___x_240_);
lean_ctor_set(v___x_242_, 5, v___x_240_);
lean_ctor_set(v___x_242_, 6, v___x_240_);
lean_ctor_set(v___x_242_, 7, v___x_240_);
lean_ctor_set(v___x_242_, 8, v___x_240_);
lean_ctor_set(v___x_242_, 9, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_unsigned_to_nat(32u);
v___x_244_ = lean_mk_empty_array_with_capacity(v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4(void){
_start:
{
size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = ((size_t)5ULL);
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_unsigned_to_nat(32u);
v___x_249_ = lean_mk_empty_array_with_capacity(v___x_248_);
v___x_250_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3);
v___x_251_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_247_);
lean_ctor_set(v___x_251_, 3, v___x_247_);
lean_ctor_set_usize(v___x_251_, 4, v___x_246_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_252_ = lean_box(1);
v___x_253_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4);
v___x_254_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
lean_ctor_set(v___x_255_, 2, v___x_252_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(lean_object* v_msgData_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; lean_object* v_env_260_; lean_object* v___x_261_; lean_object* v_scopes_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_opts_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref(v_env_260_);
lean_dec(v___x_259_);
v___x_261_ = lean_st_ref_get(v___y_257_);
v_scopes_262_ = lean_ctor_get(v___x_261_, 2);
lean_inc(v_scopes_262_);
lean_dec(v___x_261_);
v___x_263_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_264_ = l_List_head_x21___redArg(v___x_263_, v_scopes_262_);
lean_dec(v_scopes_262_);
v_opts_265_ = lean_ctor_get(v___x_264_, 1);
lean_inc_ref(v_opts_265_);
lean_dec(v___x_264_);
v___x_266_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2);
v___x_267_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5);
v___x_268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_268_, 0, v_env_260_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_267_);
lean_ctor_set(v___x_268_, 3, v_opts_265_);
v___x_269_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v_msgData_256_);
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(lean_object* v_msgData_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_271_, v___y_272_);
lean_dec(v___y_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(lean_object* v_ref_276_, lean_object* v_msgData_277_, uint8_t v_severity_278_, uint8_t v_isSilent_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___y_348_; uint8_t v___y_349_; uint8_t v___y_350_; lean_object* v___y_351_; lean_object* v___y_352_; uint8_t v___y_376_; uint8_t v___y_377_; lean_object* v___y_378_; uint8_t v___y_379_; lean_object* v___y_380_; uint8_t v___y_384_; uint8_t v___y_385_; uint8_t v___y_386_; uint8_t v___x_401_; uint8_t v___y_403_; uint8_t v___y_404_; uint8_t v___y_405_; uint8_t v___y_407_; uint8_t v___x_419_; 
v___x_401_ = 2;
v___x_419_ = l_Lean_instBEqMessageSeverity_beq(v_severity_278_, v___x_401_);
if (v___x_419_ == 0)
{
v___y_407_ = v___x_419_;
goto v___jp_406_;
}
else
{
uint8_t v___x_420_; 
lean_inc_ref(v_msgData_277_);
v___x_420_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_277_);
v___y_407_ = v___x_420_;
goto v___jp_406_;
}
v___jp_283_:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Elab_Command_getScope___redArg(v___y_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref(v___x_292_);
v___x_294_ = l_Lean_Elab_Command_getScope___redArg(v___y_291_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_330_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_330_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_330_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_330_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v_currNamespace_300_; lean_object* v_openDecls_301_; lean_object* v_env_302_; lean_object* v_messages_303_; lean_object* v_scopes_304_; lean_object* v_usedQuotCtxts_305_; lean_object* v_nextMacroScope_306_; lean_object* v_maxRecDepth_307_; lean_object* v_ngen_308_; lean_object* v_auxDeclNGen_309_; lean_object* v_infoState_310_; lean_object* v_traceState_311_; lean_object* v_snapshotTasks_312_; lean_object* v_newDecls_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_329_; 
v___x_299_ = lean_st_ref_take(v___y_291_);
v_currNamespace_300_ = lean_ctor_get(v_a_293_, 2);
lean_inc(v_currNamespace_300_);
lean_dec(v_a_293_);
v_openDecls_301_ = lean_ctor_get(v_a_295_, 3);
lean_inc(v_openDecls_301_);
lean_dec(v_a_295_);
v_env_302_ = lean_ctor_get(v___x_299_, 0);
v_messages_303_ = lean_ctor_get(v___x_299_, 1);
v_scopes_304_ = lean_ctor_get(v___x_299_, 2);
v_usedQuotCtxts_305_ = lean_ctor_get(v___x_299_, 3);
v_nextMacroScope_306_ = lean_ctor_get(v___x_299_, 4);
v_maxRecDepth_307_ = lean_ctor_get(v___x_299_, 5);
v_ngen_308_ = lean_ctor_get(v___x_299_, 6);
v_auxDeclNGen_309_ = lean_ctor_get(v___x_299_, 7);
v_infoState_310_ = lean_ctor_get(v___x_299_, 8);
v_traceState_311_ = lean_ctor_get(v___x_299_, 9);
v_snapshotTasks_312_ = lean_ctor_get(v___x_299_, 10);
v_newDecls_313_ = lean_ctor_get(v___x_299_, 11);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_329_ == 0)
{
v___x_315_ = v___x_299_;
v_isShared_316_ = v_isSharedCheck_329_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_newDecls_313_);
lean_inc(v_snapshotTasks_312_);
lean_inc(v_traceState_311_);
lean_inc(v_infoState_310_);
lean_inc(v_auxDeclNGen_309_);
lean_inc(v_ngen_308_);
lean_inc(v_maxRecDepth_307_);
lean_inc(v_nextMacroScope_306_);
lean_inc(v_usedQuotCtxts_305_);
lean_inc(v_scopes_304_);
lean_inc(v_messages_303_);
lean_inc(v_env_302_);
lean_dec(v___x_299_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_329_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v_currNamespace_300_);
lean_ctor_set(v___x_317_, 1, v_openDecls_301_);
v___x_318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___y_284_);
lean_inc_ref(v___y_289_);
lean_inc_ref(v___y_290_);
v___x_319_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_319_, 0, v___y_290_);
lean_ctor_set(v___x_319_, 1, v___y_287_);
lean_ctor_set(v___x_319_, 2, v___y_286_);
lean_ctor_set(v___x_319_, 3, v___y_289_);
lean_ctor_set(v___x_319_, 4, v___x_318_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*5, v___y_285_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*5 + 1, v___y_288_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*5 + 2, v_isSilent_279_);
v___x_320_ = l_Lean_MessageLog_add(v___x_319_, v_messages_303_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_320_);
v___x_322_ = v___x_315_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_env_302_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_scopes_304_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_usedQuotCtxts_305_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_nextMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_maxRecDepth_307_);
lean_ctor_set(v_reuseFailAlloc_328_, 6, v_ngen_308_);
lean_ctor_set(v_reuseFailAlloc_328_, 7, v_auxDeclNGen_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 8, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_328_, 9, v_traceState_311_);
lean_ctor_set(v_reuseFailAlloc_328_, 10, v_snapshotTasks_312_);
lean_ctor_set(v_reuseFailAlloc_328_, 11, v_newDecls_313_);
v___x_322_ = v_reuseFailAlloc_328_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_323_ = lean_st_ref_set(v___y_291_, v___x_322_);
v___x_324_ = lean_box(0);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_324_);
v___x_326_ = v___x_297_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_324_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
else
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_338_; 
lean_dec(v_a_293_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_284_);
v_a_331_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_338_ == 0)
{
v___x_333_ = v___x_294_;
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_294_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_338_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_a_331_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_284_);
v_a_339_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_292_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_292_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
v___jp_347_:
{
lean_object* v_fileName_353_; lean_object* v_fileMap_354_; uint8_t v_suppressElabErrors_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_374_; 
v_fileName_353_ = lean_ctor_get(v___y_280_, 0);
v_fileMap_354_ = lean_ctor_get(v___y_280_, 1);
v_suppressElabErrors_355_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*10);
v___x_356_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_277_);
v___x_357_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_356_, v___y_281_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_374_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_374_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
lean_inc_ref_n(v_fileMap_354_, 2);
v___x_362_ = l_Lean_FileMap_toPosition(v_fileMap_354_, v___y_351_);
lean_dec(v___y_351_);
v___x_363_ = l_Lean_FileMap_toPosition(v_fileMap_354_, v___y_352_);
lean_dec(v___y_352_);
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
v___x_365_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_355_ == 0)
{
lean_del_object(v___x_360_);
v___y_284_ = v_a_358_;
v___y_285_ = v___y_349_;
v___y_286_ = v___x_364_;
v___y_287_ = v___x_362_;
v___y_288_ = v___y_350_;
v___y_289_ = v___x_365_;
v___y_290_ = v_fileName_353_;
v___y_291_ = v___y_281_;
goto v___jp_283_;
}
else
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___f_368_; uint8_t v___x_369_; 
v___x_366_ = lean_box(v___y_348_);
v___x_367_ = lean_box(v_suppressElabErrors_355_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed), 3, 2);
lean_closure_set(v___f_368_, 0, v___x_366_);
lean_closure_set(v___f_368_, 1, v___x_367_);
lean_inc(v_a_358_);
v___x_369_ = l_Lean_MessageData_hasTag(v___f_368_, v_a_358_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_372_; 
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_362_);
lean_dec(v_a_358_);
v___x_370_ = lean_box(0);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_370_);
v___x_372_ = v___x_360_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
else
{
lean_del_object(v___x_360_);
v___y_284_ = v_a_358_;
v___y_285_ = v___y_349_;
v___y_286_ = v___x_364_;
v___y_287_ = v___x_362_;
v___y_288_ = v___y_350_;
v___y_289_ = v___x_365_;
v___y_290_ = v_fileName_353_;
v___y_291_ = v___y_281_;
goto v___jp_283_;
}
}
}
}
v___jp_375_:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Syntax_getTailPos_x3f(v___y_378_, v___y_377_);
lean_dec(v___y_378_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_inc(v___y_380_);
v___y_348_ = v___y_376_;
v___y_349_ = v___y_377_;
v___y_350_ = v___y_379_;
v___y_351_ = v___y_380_;
v___y_352_ = v___y_380_;
goto v___jp_347_;
}
else
{
lean_object* v_val_382_; 
v_val_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_val_382_);
lean_dec_ref(v___x_381_);
v___y_348_ = v___y_376_;
v___y_349_ = v___y_377_;
v___y_350_ = v___y_379_;
v___y_351_ = v___y_380_;
v___y_352_ = v_val_382_;
goto v___jp_347_;
}
}
v___jp_383_:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Elab_Command_getRef___redArg(v___y_280_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v_ref_389_; lean_object* v___x_390_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
v_ref_389_ = l_Lean_replaceRef(v_ref_276_, v_a_388_);
lean_dec(v_a_388_);
v___x_390_ = l_Lean_Syntax_getPos_x3f(v_ref_389_, v___y_385_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___y_376_ = v___y_384_;
v___y_377_ = v___y_385_;
v___y_378_ = v_ref_389_;
v___y_379_ = v___y_386_;
v___y_380_ = v___x_391_;
goto v___jp_375_;
}
else
{
lean_object* v_val_392_; 
v_val_392_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_val_392_);
lean_dec_ref(v___x_390_);
v___y_376_ = v___y_384_;
v___y_377_ = v___y_385_;
v___y_378_ = v_ref_389_;
v___y_379_ = v___y_386_;
v___y_380_ = v_val_392_;
goto v___jp_375_;
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_msgData_277_);
v_a_393_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_387_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_387_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
v___jp_402_:
{
if (v___y_405_ == 0)
{
v___y_384_ = v___y_403_;
v___y_385_ = v___y_404_;
v___y_386_ = v_severity_278_;
goto v___jp_383_;
}
else
{
v___y_384_ = v___y_403_;
v___y_385_ = v___y_404_;
v___y_386_ = v___x_401_;
goto v___jp_383_;
}
}
v___jp_406_:
{
if (v___y_407_ == 0)
{
lean_object* v___x_408_; lean_object* v_scopes_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_opts_412_; uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_408_ = lean_st_ref_get(v___y_281_);
v_scopes_409_ = lean_ctor_get(v___x_408_, 2);
lean_inc(v_scopes_409_);
lean_dec(v___x_408_);
v___x_410_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_411_ = l_List_head_x21___redArg(v___x_410_, v_scopes_409_);
lean_dec(v_scopes_409_);
v_opts_412_ = lean_ctor_get(v___x_411_, 1);
lean_inc_ref(v_opts_412_);
lean_dec(v___x_411_);
v___x_413_ = 1;
v___x_414_ = l_Lean_instBEqMessageSeverity_beq(v_severity_278_, v___x_413_);
if (v___x_414_ == 0)
{
lean_dec_ref(v_opts_412_);
v___y_403_ = v___y_407_;
v___y_404_ = v___y_407_;
v___y_405_ = v___x_414_;
goto v___jp_402_;
}
else
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = l_Lean_warningAsError;
v___x_416_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_412_, v___x_415_);
lean_dec_ref(v_opts_412_);
v___y_403_ = v___y_407_;
v___y_404_ = v___y_407_;
v___y_405_ = v___x_416_;
goto v___jp_402_;
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v_msgData_277_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object* v_ref_421_, lean_object* v_msgData_422_, lean_object* v_severity_423_, lean_object* v_isSilent_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v_severity_boxed_428_; uint8_t v_isSilent_boxed_429_; lean_object* v_res_430_; 
v_severity_boxed_428_ = lean_unbox(v_severity_423_);
v_isSilent_boxed_429_ = lean_unbox(v_isSilent_424_);
v_res_430_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_421_, v_msgData_422_, v_severity_boxed_428_, v_isSilent_boxed_429_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v_ref_421_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object* v_ref_431_, lean_object* v_msgData_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = 1;
v___x_437_ = 0;
v___x_438_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_431_, v_msgData_432_, v___x_436_, v___x_437_, v___y_433_, v___y_434_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object* v_ref_439_, lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_439_, v_msgData_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v_ref_439_);
return v_res_444_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0));
v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* v_linterOption_451_, lean_object* v_stx_452_, lean_object* v_msg_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_name_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_472_; 
v_name_457_ = lean_ctor_get(v_linterOption_451_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_linterOption_451_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_linterOption_451_, 1);
lean_dec(v_unused_473_);
v___x_459_ = v_linterOption_451_;
v_isShared_460_ = v_isSharedCheck_472_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_name_457_);
lean_dec(v_linterOption_451_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_472_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_461_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
lean_inc(v_name_457_);
v___x_462_ = l_Lean_MessageData_ofName(v_name_457_);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 7);
lean_ctor_set(v___x_459_, 1, v___x_462_);
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_464_ = v___x_459_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_462_);
v___x_464_ = v_reuseFailAlloc_471_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_disable_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v_disable_467_ = l_Lean_MessageData_note(v___x_466_);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v_msg_453_);
lean_ctor_set(v___x_468_, 1, v_disable_467_);
v___x_469_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_469_, 0, v_name_457_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_452_, v___x_469_, v___y_454_, v___y_455_);
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_474_, lean_object* v_stx_475_, lean_object* v_msg_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_474_, v_stx_475_, v_msg_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v_stx_475_);
return v_res_480_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_499_, size_t v_sz_500_, size_t v_i_501_, lean_object* v_b_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_lt(v_i_501_, v_sz_500_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v_b_502_);
return v___x_507_;
}
else
{
lean_object* v_a_508_; lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_554_; 
v_a_508_ = lean_array_uget(v_as_499_, v_i_501_);
v_snd_509_ = lean_ctor_get(v_a_508_, 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_a_508_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; 
v_unused_555_ = lean_ctor_get(v_a_508_, 0);
lean_dec(v_unused_555_);
v___x_511_ = v_a_508_;
v_isShared_512_ = v_isSharedCheck_554_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_dec(v_a_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_554_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_snd_513_; lean_object* v_fst_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_553_; 
v_snd_513_ = lean_ctor_get(v_snd_509_, 1);
v_fst_514_ = lean_ctor_get(v_snd_509_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v_snd_509_);
if (v_isSharedCheck_553_ == 0)
{
v___x_516_ = v_snd_509_;
v_isShared_517_ = v_isSharedCheck_553_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_snd_513_);
lean_inc(v_fst_514_);
lean_dec(v_snd_509_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_553_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_fst_518_; lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_552_; 
v_fst_518_ = lean_ctor_get(v_snd_513_, 0);
v_snd_519_ = lean_ctor_get(v_snd_513_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_snd_513_);
if (v_isSharedCheck_552_ == 0)
{
v___x_521_ = v_snd_513_;
v_isShared_522_ = v_isSharedCheck_552_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_inc(v_fst_518_);
lean_dec(v_snd_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_552_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_525_ = l_Lean_MessageData_ofName(v_fst_518_);
lean_inc_ref(v___x_525_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 7);
lean_ctor_set(v___x_521_, 1, v___x_525_);
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_527_ = v___x_521_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_525_);
v___x_527_ = v_reuseFailAlloc_551_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 7);
lean_ctor_set(v___x_516_, 1, v___x_528_);
lean_ctor_set(v___x_516_, 0, v___x_527_);
v___x_530_ = v___x_516_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_527_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_528_);
v___x_530_ = v_reuseFailAlloc_550_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = l_Lean_MessageData_ofName(v_snd_519_);
lean_inc_ref(v___x_531_);
if (v_isShared_512_ == 0)
{
lean_ctor_set_tag(v___x_511_, 7);
lean_ctor_set(v___x_511_, 1, v___x_531_);
lean_ctor_set(v___x_511_, 0, v___x_530_);
v___x_533_ = v___x_511_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_549_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_525_);
v___x_538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v___x_531_);
v___x_541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_535_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_523_, v_fst_514_, v___x_543_, v___y_503_, v___y_504_);
lean_dec(v_fst_514_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; size_t v___x_546_; size_t v___x_547_; 
lean_dec_ref(v___x_544_);
v___x_545_ = lean_box(0);
v___x_546_ = ((size_t)1ULL);
v___x_547_ = lean_usize_add(v_i_501_, v___x_546_);
v_i_501_ = v___x_547_;
v_b_502_ = v___x_545_;
goto _start;
}
else
{
return v___x_544_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_556_, lean_object* v_sz_557_, lean_object* v_i_558_, lean_object* v_b_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
size_t v_sz_boxed_563_; size_t v_i_boxed_564_; lean_object* v_res_565_; 
v_sz_boxed_563_ = lean_unbox_usize(v_sz_557_);
lean_dec(v_sz_557_);
v_i_boxed_564_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_res_565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_556_, v_sz_boxed_563_, v_i_boxed_564_, v_b_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec_ref(v_as_556_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = lean_box(v___x_566_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_22315__boxed_582_; lean_object* v_res_583_; 
v___x_22315__boxed_582_ = lean_unbox(v___x_575_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22315__boxed_582_, v_x_576_, v_x_577_, v_x_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v_x_578_);
lean_dec_ref(v_x_577_);
lean_dec_ref(v_x_576_);
return v_res_583_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
uint8_t v___x_586_; 
v___x_586_ = 0;
return v___x_586_;
}
else
{
lean_object* v_key_587_; lean_object* v_tail_588_; uint8_t v___x_589_; 
v_key_587_ = lean_ctor_get(v_x_585_, 0);
v_tail_588_ = lean_ctor_get(v_x_585_, 2);
v___x_589_ = l_Lean_Syntax_instBEqRange_beq(v_key_587_, v_a_584_);
if (v___x_589_ == 0)
{
v_x_585_ = v_tail_588_;
goto _start;
}
else
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_591_, lean_object* v_x_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_591_, v_x_592_);
lean_dec(v_x_592_);
lean_dec_ref(v_a_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_buckets_597_; lean_object* v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v_fold_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_buckets_597_ = lean_ctor_get(v_m_595_, 1);
v___x_598_ = lean_array_get_size(v_buckets_597_);
v___x_599_ = l_Lean_Syntax_instHashableRange_hash(v_a_596_);
v___x_600_ = 32ULL;
v___x_601_ = lean_uint64_shift_right(v___x_599_, v___x_600_);
v_fold_602_ = lean_uint64_xor(v___x_599_, v___x_601_);
v___x_603_ = 16ULL;
v___x_604_ = lean_uint64_shift_right(v_fold_602_, v___x_603_);
v___x_605_ = lean_uint64_xor(v_fold_602_, v___x_604_);
v___x_606_ = lean_uint64_to_usize(v___x_605_);
v___x_607_ = lean_usize_of_nat(v___x_598_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_sub(v___x_607_, v___x_608_);
v___x_610_ = lean_usize_land(v___x_606_, v___x_609_);
v___x_611_ = lean_array_uget_borrowed(v_buckets_597_, v___x_610_);
v___x_612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_596_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_613_, lean_object* v_a_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_613_, v_a_614_);
lean_dec_ref(v_a_614_);
lean_dec_ref(v_m_613_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_617_, lean_object* v_b_618_, lean_object* v_x_619_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_dec(v_b_618_);
lean_dec_ref(v_a_617_);
return v_x_619_;
}
else
{
lean_object* v_key_620_; lean_object* v_value_621_; lean_object* v_tail_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_634_; 
v_key_620_ = lean_ctor_get(v_x_619_, 0);
v_value_621_ = lean_ctor_get(v_x_619_, 1);
v_tail_622_ = lean_ctor_get(v_x_619_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_619_);
if (v_isSharedCheck_634_ == 0)
{
v___x_624_ = v_x_619_;
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_tail_622_);
lean_inc(v_value_621_);
lean_inc(v_key_620_);
lean_dec(v_x_619_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_634_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
uint8_t v___x_626_; 
v___x_626_ = l_Lean_Syntax_instBEqRange_beq(v_key_620_, v_a_617_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_617_, v_b_618_, v_tail_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_627_);
v___x_629_ = v___x_624_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_key_620_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_value_621_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
else
{
lean_object* v___x_632_; 
lean_dec(v_value_621_);
lean_dec(v_key_620_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_b_618_);
lean_ctor_set(v___x_624_, 0, v_a_617_);
v___x_632_ = v___x_624_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_617_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_b_618_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_tail_622_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
return v_x_635_;
}
else
{
lean_object* v_key_637_; lean_object* v_value_638_; lean_object* v_tail_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_662_; 
v_key_637_ = lean_ctor_get(v_x_636_, 0);
v_value_638_ = lean_ctor_get(v_x_636_, 1);
v_tail_639_ = lean_ctor_get(v_x_636_, 2);
v_isSharedCheck_662_ = !lean_is_exclusive(v_x_636_);
if (v_isSharedCheck_662_ == 0)
{
v___x_641_ = v_x_636_;
v_isShared_642_ = v_isSharedCheck_662_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_tail_639_);
lean_inc(v_value_638_);
lean_inc(v_key_637_);
lean_dec(v_x_636_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_662_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v_fold_647_; uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_643_ = lean_array_get_size(v_x_635_);
v___x_644_ = l_Lean_Syntax_instHashableRange_hash(v_key_637_);
v___x_645_ = 32ULL;
v___x_646_ = lean_uint64_shift_right(v___x_644_, v___x_645_);
v_fold_647_ = lean_uint64_xor(v___x_644_, v___x_646_);
v___x_648_ = 16ULL;
v___x_649_ = lean_uint64_shift_right(v_fold_647_, v___x_648_);
v___x_650_ = lean_uint64_xor(v_fold_647_, v___x_649_);
v___x_651_ = lean_uint64_to_usize(v___x_650_);
v___x_652_ = lean_usize_of_nat(v___x_643_);
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_sub(v___x_652_, v___x_653_);
v___x_655_ = lean_usize_land(v___x_651_, v___x_654_);
v___x_656_ = lean_array_uget_borrowed(v_x_635_, v___x_655_);
lean_inc(v___x_656_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 2, v___x_656_);
v___x_658_ = v___x_641_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_key_637_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_value_638_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v___x_656_);
v___x_658_ = v_reuseFailAlloc_661_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_659_; 
v___x_659_ = lean_array_uset(v_x_635_, v___x_655_, v___x_658_);
v_x_635_ = v___x_659_;
v_x_636_ = v_tail_639_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_663_, lean_object* v_source_664_, lean_object* v_target_665_){
_start:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_get_size(v_source_664_);
v___x_667_ = lean_nat_dec_lt(v_i_663_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v_source_664_);
lean_dec(v_i_663_);
return v_target_665_;
}
else
{
lean_object* v_es_668_; lean_object* v___x_669_; lean_object* v_source_670_; lean_object* v_target_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_es_668_ = lean_array_fget(v_source_664_, v_i_663_);
v___x_669_ = lean_box(0);
v_source_670_ = lean_array_fset(v_source_664_, v_i_663_, v___x_669_);
v_target_671_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_665_, v_es_668_);
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v_i_663_, v___x_672_);
lean_dec(v_i_663_);
v_i_663_ = v___x_673_;
v_source_664_ = v_source_670_;
v_target_665_ = v_target_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_nbuckets_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_676_ = lean_array_get_size(v_data_675_);
v___x_677_ = lean_unsigned_to_nat(2u);
v_nbuckets_678_ = lean_nat_mul(v___x_676_, v___x_677_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_box(0);
v___x_681_ = lean_mk_array(v_nbuckets_678_, v___x_680_);
v___x_682_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_679_, v_data_675_, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_b_685_){
_start:
{
lean_object* v_size_686_; lean_object* v_buckets_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_730_; 
v_size_686_ = lean_ctor_get(v_m_683_, 0);
v_buckets_687_ = lean_ctor_get(v_m_683_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_m_683_);
if (v_isSharedCheck_730_ == 0)
{
v___x_689_ = v_m_683_;
v_isShared_690_ = v_isSharedCheck_730_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_buckets_687_);
lean_inc(v_size_686_);
lean_dec(v_m_683_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_730_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v_fold_695_; uint64_t v___x_696_; uint64_t v___x_697_; uint64_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; lean_object* v_bkt_704_; uint8_t v___x_705_; 
v___x_691_ = lean_array_get_size(v_buckets_687_);
v___x_692_ = l_Lean_Syntax_instHashableRange_hash(v_a_684_);
v___x_693_ = 32ULL;
v___x_694_ = lean_uint64_shift_right(v___x_692_, v___x_693_);
v_fold_695_ = lean_uint64_xor(v___x_692_, v___x_694_);
v___x_696_ = 16ULL;
v___x_697_ = lean_uint64_shift_right(v_fold_695_, v___x_696_);
v___x_698_ = lean_uint64_xor(v_fold_695_, v___x_697_);
v___x_699_ = lean_uint64_to_usize(v___x_698_);
v___x_700_ = lean_usize_of_nat(v___x_691_);
v___x_701_ = ((size_t)1ULL);
v___x_702_ = lean_usize_sub(v___x_700_, v___x_701_);
v___x_703_ = lean_usize_land(v___x_699_, v___x_702_);
v_bkt_704_ = lean_array_uget_borrowed(v_buckets_687_, v___x_703_);
v___x_705_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_684_, v_bkt_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v_size_x27_707_; lean_object* v___x_708_; lean_object* v_buckets_x27_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_706_ = lean_unsigned_to_nat(1u);
v_size_x27_707_ = lean_nat_add(v_size_686_, v___x_706_);
lean_dec(v_size_686_);
lean_inc(v_bkt_704_);
v___x_708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_708_, 0, v_a_684_);
lean_ctor_set(v___x_708_, 1, v_b_685_);
lean_ctor_set(v___x_708_, 2, v_bkt_704_);
v_buckets_x27_709_ = lean_array_uset(v_buckets_687_, v___x_703_, v___x_708_);
v___x_710_ = lean_unsigned_to_nat(4u);
v___x_711_ = lean_nat_mul(v_size_x27_707_, v___x_710_);
v___x_712_ = lean_unsigned_to_nat(3u);
v___x_713_ = lean_nat_div(v___x_711_, v___x_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_array_get_size(v_buckets_x27_709_);
v___x_715_ = lean_nat_dec_le(v___x_713_, v___x_714_);
lean_dec(v___x_713_);
if (v___x_715_ == 0)
{
lean_object* v_val_716_; lean_object* v___x_718_; 
v_val_716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_709_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v_val_716_);
lean_ctor_set(v___x_689_, 0, v_size_x27_707_);
v___x_718_ = v___x_689_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_size_x27_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_val_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
else
{
lean_object* v___x_721_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v_buckets_x27_709_);
lean_ctor_set(v___x_689_, 0, v_size_x27_707_);
v___x_721_ = v___x_689_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_size_x27_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_buckets_x27_709_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v___x_723_; lean_object* v_buckets_x27_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
lean_inc(v_bkt_704_);
v___x_723_ = lean_box(0);
v_buckets_x27_724_ = lean_array_uset(v_buckets_687_, v___x_703_, v___x_723_);
v___x_725_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_684_, v_b_685_, v_bkt_704_);
v___x_726_ = lean_array_uset(v_buckets_x27_724_, v___x_703_, v___x_725_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_726_);
v___x_728_ = v___x_689_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_size_686_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_731_, lean_object* v_val_732_, lean_object* v_info_733_, lean_object* v___x_734_, lean_object* v_val_735_, uint8_t v___x_736_, lean_object* v_as_x27_737_, lean_object* v_b_738_, lean_object* v___y_739_){
_start:
{
if (lean_obj_tag(v_as_x27_737_) == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v_val_735_);
lean_dec(v___x_734_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_b_738_);
return v___x_741_;
}
else
{
lean_object* v_head_742_; lean_object* v_tail_743_; lean_object* v___x_744_; lean_object* v_env_745_; lean_object* v___x_746_; lean_object* v___x_759_; 
v_head_742_ = lean_ctor_get(v_as_x27_737_, 0);
v_tail_743_ = lean_ctor_get(v_as_x27_737_, 1);
v___x_744_ = lean_st_ref_get(v___y_739_);
v_env_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_env_745_);
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
lean_inc(v_head_742_);
v___x_759_ = l_Lean_Environment_find_x3f(v_env_745_, v_head_742_, v___x_736_);
if (lean_obj_tag(v___x_759_) == 1)
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_val_760_);
lean_dec_ref(v___x_759_);
if (lean_obj_tag(v_val_760_) == 6)
{
lean_object* v_val_761_; lean_object* v_numFields_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_val_761_ = lean_ctor_get(v_val_760_, 0);
lean_inc_ref(v_val_761_);
lean_dec_ref(v_val_760_);
v_numFields_762_ = lean_ctor_get(v_val_761_, 4);
lean_inc(v_numFields_762_);
lean_dec_ref(v_val_761_);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_nat_dec_lt(v___x_763_, v_numFields_762_);
lean_dec(v_numFields_762_);
if (v___x_764_ == 0)
{
goto v___jp_747_;
}
else
{
v_as_x27_737_ = v_tail_743_;
v_b_738_ = v___x_746_;
goto _start;
}
}
else
{
lean_dec(v_val_760_);
goto v___jp_747_;
}
}
else
{
lean_dec(v___x_759_);
goto v___jp_747_;
}
v___jp_747_:
{
if (lean_obj_tag(v_head_742_) == 1)
{
lean_object* v_str_748_; uint8_t v___x_749_; 
v_str_748_ = lean_ctor_get(v_head_742_, 1);
v___x_749_ = lean_string_dec_eq(v_str_748_, v_str_731_);
if (v___x_749_ == 0)
{
v_as_x27_737_ = v_tail_743_;
v_b_738_ = v___x_746_;
goto _start;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_751_ = lean_st_ref_take(v_val_732_);
v___x_752_ = l_Lean_Elab_Info_stx(v_info_733_);
lean_inc_ref(v_head_742_);
lean_inc(v___x_734_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_734_);
lean_ctor_set(v___x_753_, 1, v_head_742_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
lean_inc_ref(v_val_735_);
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_751_, v_val_735_, v___x_754_);
v___x_756_ = lean_st_ref_set(v_val_732_, v___x_755_);
v_as_x27_737_ = v_tail_743_;
v_b_738_ = v___x_746_;
goto _start;
}
}
else
{
v_as_x27_737_ = v_tail_743_;
v_b_738_ = v___x_746_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_766_, lean_object* v_val_767_, lean_object* v_info_768_, lean_object* v___x_769_, lean_object* v_val_770_, lean_object* v___x_771_, lean_object* v_as_x27_772_, lean_object* v_b_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
uint8_t v___x_22579__boxed_776_; lean_object* v_res_777_; 
v___x_22579__boxed_776_ = lean_unbox(v___x_771_);
v_res_777_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_766_, v_val_767_, v_info_768_, v___x_769_, v_val_770_, v___x_22579__boxed_776_, v_as_x27_772_, v_b_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec(v_as_x27_772_);
lean_dec_ref(v_info_768_);
lean_dec(v_val_767_);
lean_dec_ref(v_str_766_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_778_, v___y_780_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v___x_786_ = lean_whnf(v_a_785_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
return v___x_786_;
}
else
{
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_794_, lean_object* v___x_795_, lean_object* v_val_796_, lean_object* v___x_797_, lean_object* v_ci_798_, lean_object* v_info_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
if (lean_obj_tag(v_info_799_) == 1)
{
lean_object* v_i_804_; lean_object* v_expr_805_; 
v_i_804_ = lean_ctor_get(v_info_799_, 0);
v_expr_805_ = lean_ctor_get(v_i_804_, 3);
if (lean_obj_tag(v_expr_805_) == 1)
{
lean_object* v_lctx_806_; lean_object* v_expectedType_x3f_807_; uint8_t v_isBinder_808_; lean_object* v_fvarId_809_; lean_object* v___x_810_; 
v_lctx_806_ = lean_ctor_get(v_i_804_, 1);
v_expectedType_x3f_807_ = lean_ctor_get(v_i_804_, 2);
v_isBinder_808_ = lean_ctor_get_uint8(v_i_804_, sizeof(void*)*4);
v_fvarId_809_ = lean_ctor_get(v_expr_805_, 0);
v___x_810_ = l_Lean_Elab_Info_range_x3f(v_info_799_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_966_; 
v_val_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_966_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_966_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_val_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_966_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = lean_st_ref_get(v_val_794_);
v___x_816_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_815_, v_val_811_);
lean_dec(v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = l_Lean_Elab_Info_stx(v_info_799_);
v___x_818_ = l_Lean_Syntax_getHeadInfo(v___x_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_dec_ref(v___x_818_);
if (v_isBinder_808_ == 0)
{
lean_object* v___x_820_; 
lean_dec(v___x_817_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 0, v___x_795_);
v___x_820_ = v___x_813_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_795_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_822_; 
lean_inc(v_fvarId_809_);
lean_inc_ref(v_lctx_806_);
v___x_822_ = lean_local_ctx_find(v_lctx_806_, v_fvarId_809_);
if (lean_obj_tag(v___x_822_) == 1)
{
lean_object* v_val_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_956_; 
v_val_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_956_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_956_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_val_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_956_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_start_827_; uint8_t v___x_828_; 
v_start_827_ = lean_ctor_get(v_val_811_, 0);
v___x_828_ = l_Lean_Syntax_Range_contains(v_val_796_, v_start_827_, v___x_816_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v_val_823_);
lean_dec(v___x_817_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_795_);
v___x_830_ = v___x_825_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_795_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
if (v___x_816_ == 0)
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = l_Lean_LocalDecl_userName(v_val_823_);
lean_dec(v_val_823_);
v___x_833_ = l_Lean_Name_hasMacroScopes(v___x_832_);
lean_dec(v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v_toCommandContextInfo_834_; lean_object* v_options_835_; lean_object* v___x_836_; 
v_toCommandContextInfo_834_ = lean_ctor_get(v_ci_798_, 0);
v_options_835_ = lean_ctor_get(v_toCommandContextInfo_834_, 4);
lean_inc_ref(v_options_835_);
v___x_836_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_835_, v___y_802_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_941_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_941_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_941_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_941_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_Linter_getLinterValue(v___x_797_, v_a_837_);
lean_dec(v_a_837_);
if (v___x_841_ == 0)
{
lean_object* v___x_843_; 
lean_del_object(v___x_825_);
lean_dec(v___x_817_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_795_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_795_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Syntax_getId(v___x_817_);
lean_dec(v___x_817_);
if (lean_obj_tag(v___x_845_) == 1)
{
lean_object* v_pre_846_; lean_object* v_str_847_; lean_object* v_ty_849_; lean_object* v___y_850_; lean_object* v___y_851_; 
v_pre_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_pre_846_);
v_str_847_ = lean_ctor_get(v___x_845_, 1);
lean_inc_ref(v_str_847_);
if (lean_obj_tag(v_pre_846_) == 0)
{
lean_del_object(v___x_839_);
if (lean_obj_tag(v_expectedType_x3f_807_) == 1)
{
lean_object* v_val_908_; 
lean_del_object(v___x_813_);
v_val_908_ = lean_ctor_get(v_expectedType_x3f_807_, 0);
lean_inc(v_val_908_);
v_ty_849_ = v_val_908_;
v___y_850_ = v___y_801_;
v___y_851_ = v___y_802_;
goto v___jp_848_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_inc_ref(v_expr_805_);
v___x_909_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_909_, 0, v_expr_805_);
lean_inc_ref(v_ci_798_);
lean_inc_ref(v_i_804_);
v___x_910_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_804_, v_ci_798_, v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; 
lean_del_object(v___x_813_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
v_ty_849_ = v_a_911_;
v___y_850_ = v___y_801_;
v___y_851_ = v___y_802_;
goto v___jp_848_;
}
else
{
lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_str_847_);
lean_dec_ref(v___x_845_);
lean_del_object(v___x_825_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
v_isSharedCheck_932_ = !lean_is_exclusive(v_val_811_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; lean_object* v_unused_934_; 
v_unused_933_ = lean_ctor_get(v_val_811_, 1);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_val_811_, 0);
lean_dec(v_unused_934_);
v___x_913_ = v_val_811_;
v_isShared_914_ = v_isSharedCheck_932_;
goto v_resetjp_912_;
}
else
{
lean_dec(v_val_811_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_932_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_931_; 
v_a_915_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_931_ == 0)
{
v___x_917_ = v___x_910_;
v_isShared_918_ = v_isSharedCheck_931_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_910_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_931_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_ref_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v_ref_919_ = lean_ctor_get(v___y_801_, 7);
v___x_920_ = lean_io_error_to_string(v_a_915_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 3);
lean_ctor_set(v___x_813_, 0, v___x_920_);
v___x_922_ = v___x_813_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_930_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = l_Lean_MessageData_ofFormat(v___x_922_);
lean_inc(v_ref_919_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 1, v___x_923_);
lean_ctor_set(v___x_913_, 0, v_ref_919_);
v___x_925_ = v___x_913_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_ref_919_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___x_923_);
v___x_925_ = v_reuseFailAlloc_929_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_927_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_925_);
v___x_927_ = v___x_917_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
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
lean_object* v___x_936_; 
lean_dec_ref(v_str_847_);
lean_dec_ref(v___x_845_);
lean_dec(v_pre_846_);
lean_del_object(v___x_825_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_795_);
v___x_936_ = v___x_839_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_795_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
v___jp_848_:
{
lean_object* v___f_852_; lean_object* v___x_853_; 
v___f_852_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_852_, 0, v_ty_849_);
lean_inc_ref(v_i_804_);
v___x_853_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_804_, v_ci_798_, v___f_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_884_; 
lean_del_object(v___x_825_);
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_884_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_884_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_884_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Expr_getAppFn_x27(v_a_854_);
lean_dec(v_a_854_);
if (lean_obj_tag(v___x_858_) == 4)
{
lean_object* v_declName_859_; lean_object* v___x_860_; lean_object* v_env_861_; lean_object* v___x_862_; 
v_declName_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_declName_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = lean_st_ref_get(v___y_851_);
v_env_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_env_861_);
lean_dec(v___x_860_);
v___x_862_ = l_Lean_Environment_find_x3f(v_env_861_, v_declName_859_, v___x_816_);
if (lean_obj_tag(v___x_862_) == 1)
{
lean_object* v_val_863_; 
v_val_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_val_863_);
lean_dec_ref(v___x_862_);
if (lean_obj_tag(v_val_863_) == 5)
{
lean_object* v_val_864_; lean_object* v_ctors_865_; lean_object* v___x_866_; 
lean_del_object(v___x_856_);
v_val_864_ = lean_ctor_get(v_val_863_, 0);
lean_inc_ref(v_val_864_);
lean_dec_ref(v_val_863_);
v_ctors_865_ = lean_ctor_get(v_val_864_, 4);
lean_inc(v_ctors_865_);
lean_dec_ref(v_val_864_);
v___x_866_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_847_, v_val_794_, v_info_799_, v___x_845_, v_val_811_, v___x_816_, v_ctors_865_, v___x_795_, v___y_851_);
lean_dec(v_ctors_865_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_str_847_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_873_ == 0)
{
lean_object* v_unused_874_; 
v_unused_874_ = lean_ctor_get(v___x_866_, 0);
lean_dec(v_unused_874_);
v___x_868_ = v___x_866_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_dec(v___x_866_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_795_);
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_795_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
else
{
return v___x_866_;
}
}
else
{
lean_object* v___x_876_; 
lean_dec(v_val_863_);
lean_dec_ref(v_str_847_);
lean_dec_ref(v___x_845_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_795_);
v___x_876_ = v___x_856_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_795_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
else
{
lean_object* v___x_879_; 
lean_dec(v___x_862_);
lean_dec_ref(v_str_847_);
lean_dec_ref(v___x_845_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_795_);
v___x_879_ = v___x_856_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_795_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
else
{
lean_object* v___x_882_; 
lean_dec_ref(v___x_858_);
lean_dec_ref(v_str_847_);
lean_dec_ref(v___x_845_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_795_);
v___x_882_ = v___x_856_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_795_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v_str_847_);
lean_dec_ref(v___x_845_);
lean_dec_ref(v_info_799_);
v_isSharedCheck_905_ = !lean_is_exclusive(v_val_811_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; lean_object* v_unused_907_; 
v_unused_906_ = lean_ctor_get(v_val_811_, 1);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_val_811_, 0);
lean_dec(v_unused_907_);
v___x_886_ = v_val_811_;
v_isShared_887_ = v_isSharedCheck_905_;
goto v_resetjp_885_;
}
else
{
lean_dec(v_val_811_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_905_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_904_; 
v_a_888_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_904_ == 0)
{
v___x_890_ = v___x_853_;
v_isShared_891_ = v_isSharedCheck_904_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_853_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_904_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_ref_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v_ref_892_ = lean_ctor_get(v___y_850_, 7);
v___x_893_ = lean_io_error_to_string(v_a_888_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 3);
lean_ctor_set(v___x_825_, 0, v___x_893_);
v___x_895_ = v___x_825_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_903_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = l_Lean_MessageData_ofFormat(v___x_895_);
lean_inc(v_ref_892_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_896_);
lean_ctor_set(v___x_886_, 0, v_ref_892_);
v___x_898_ = v___x_886_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_ref_892_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_896_);
v___x_898_ = v_reuseFailAlloc_902_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_898_);
v___x_900_ = v___x_890_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
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
lean_object* v___x_939_; 
lean_dec(v___x_845_);
lean_del_object(v___x_825_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_795_);
v___x_939_ = v___x_839_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_795_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_del_object(v___x_825_);
lean_dec(v___x_817_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
v_a_942_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_836_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_836_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v___x_951_; 
lean_dec(v___x_817_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_795_);
v___x_951_ = v___x_825_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_795_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v___x_954_; 
lean_dec(v_val_823_);
lean_dec(v___x_817_);
lean_del_object(v___x_813_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_795_);
v___x_954_ = v___x_825_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_795_);
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
}
else
{
lean_object* v___x_958_; 
lean_dec(v___x_822_);
lean_dec(v___x_817_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 0, v___x_795_);
v___x_958_ = v___x_813_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_795_);
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
lean_object* v___x_961_; 
lean_dec(v___x_818_);
lean_dec(v___x_817_);
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 0, v___x_795_);
v___x_961_ = v___x_813_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_795_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v_val_811_);
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 0, v___x_795_);
v___x_964_ = v___x_813_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_795_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v___x_810_);
lean_dec_ref(v_ci_798_);
v_isSharedCheck_973_ = !lean_is_exclusive(v_info_799_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v_info_799_, 0);
lean_dec(v_unused_974_);
v___x_968_ = v_info_799_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_dec(v_info_799_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
lean_ctor_set_tag(v___x_968_, 0);
lean_ctor_set(v___x_968_, 0, v___x_795_);
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_795_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v_ci_798_);
v_isSharedCheck_981_ = !lean_is_exclusive(v_info_799_);
if (v_isSharedCheck_981_ == 0)
{
lean_object* v_unused_982_; 
v_unused_982_ = lean_ctor_get(v_info_799_, 0);
lean_dec(v_unused_982_);
v___x_976_ = v_info_799_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_dec(v_info_799_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set_tag(v___x_976_, 0);
lean_ctor_set(v___x_976_, 0, v___x_795_);
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_795_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_983_; 
lean_dec_ref(v_info_799_);
lean_dec_ref(v_ci_798_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_795_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_984_, lean_object* v___x_985_, lean_object* v_val_986_, lean_object* v___x_987_, lean_object* v_ci_988_, lean_object* v_info_989_, lean_object* v_x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_984_, v___x_985_, v_val_986_, v___x_987_, v_ci_988_, v_info_989_, v_x_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_x_990_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v_val_986_);
lean_dec(v_val_984_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_995_, lean_object* v_ci_996_, lean_object* v_i_997_, lean_object* v_cs_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
lean_inc(v___y_1001_);
lean_inc_ref(v___y_1000_);
v___x_1003_ = lean_apply_6(v_postNode_995_, v_ci_996_, v_i_997_, v_cs_998_, v___y_1000_, v___y_1001_, lean_box(0));
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1004_, lean_object* v_ci_1005_, lean_object* v_i_1006_, lean_object* v_cs_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1004_, v_ci_1005_, v_i_1006_, v_cs_1007_, v_x_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v_x_1008_);
return v_res_1012_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_instMonadEIO(lean_box(0));
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_toApplicative_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1053_; 
v___x_1020_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1021_ = l_StateRefT_x27_instMonad___redArg(v___x_1020_);
v_toApplicative_1022_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1021_, 1);
lean_dec(v_unused_1054_);
v___x_1024_ = v___x_1021_;
v_isShared_1025_ = v_isSharedCheck_1053_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_toApplicative_1022_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1053_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_toFunctor_1026_; lean_object* v_toSeq_1027_; lean_object* v_toSeqLeft_1028_; lean_object* v_toSeqRight_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1051_; 
v_toFunctor_1026_ = lean_ctor_get(v_toApplicative_1022_, 0);
v_toSeq_1027_ = lean_ctor_get(v_toApplicative_1022_, 2);
v_toSeqLeft_1028_ = lean_ctor_get(v_toApplicative_1022_, 3);
v_toSeqRight_1029_ = lean_ctor_get(v_toApplicative_1022_, 4);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_toApplicative_1022_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_toApplicative_1022_, 1);
lean_dec(v_unused_1052_);
v___x_1031_ = v_toApplicative_1022_;
v_isShared_1032_ = v_isSharedCheck_1051_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_toSeqRight_1029_);
lean_inc(v_toSeqLeft_1028_);
lean_inc(v_toSeq_1027_);
lean_inc(v_toFunctor_1026_);
lean_dec(v_toApplicative_1022_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1051_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___x_1042_; 
v___f_1033_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1034_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1026_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toFunctor_1026_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toFunctor_1026_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___f_1035_);
lean_ctor_set(v___x_1037_, 1, v___f_1036_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toSeqRight_1029_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeqLeft_1028_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeq_1027_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 4, v___f_1038_);
lean_ctor_set(v___x_1031_, 3, v___f_1039_);
lean_ctor_set(v___x_1031_, 2, v___f_1040_);
lean_ctor_set(v___x_1031_, 1, v___f_1033_);
lean_ctor_set(v___x_1031_, 0, v___x_1037_);
v___x_1042_ = v___x_1031_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___f_1033_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v___f_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v___f_1038_);
v___x_1042_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1044_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v___f_1034_);
lean_ctor_set(v___x_1024_, 0, v___x_1042_);
v___x_1044_ = v___x_1024_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___f_1034_);
v___x_1044_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_18809__overap_1047_; lean_object* v___x_1048_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = l_instInhabitedOfMonad___redArg(v___x_1044_, v___x_1045_);
v___x_18809__overap_1047_ = lean_panic_fn_borrowed(v___x_1046_, v_msg_1016_);
lean_dec(v___x_1046_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
v___x_1048_ = lean_apply_3(v___x_18809__overap_1047_, v___y_1017_, v___y_1018_, lean_box(0));
return v___x_1048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1059_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1063_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1064_ = lean_unsigned_to_nat(21u);
v___x_1065_ = lean_unsigned_to_nat(65u);
v___x_1066_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1067_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1068_ = l_mkPanicMessageWithDecl(v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_, v___x_1063_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1069_, lean_object* v_postNode_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
switch(lean_obj_tag(v_x_1072_))
{
case 0:
{
lean_object* v_i_1076_; lean_object* v_t_1077_; lean_object* v___x_1078_; 
v_i_1076_ = lean_ctor_get(v_x_1072_, 0);
lean_inc_ref(v_i_1076_);
v_t_1077_ = lean_ctor_get(v_x_1072_, 1);
lean_inc_ref(v_t_1077_);
lean_dec_ref(v_x_1072_);
v___x_1078_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1076_, v_x_1071_);
v_x_1071_ = v___x_1078_;
v_x_1072_ = v_t_1077_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v_x_1072_);
lean_dec_ref(v_postNode_1070_);
lean_dec_ref(v_preNode_1069_);
v___x_1080_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1081_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1080_, v___y_1073_, v___y_1074_);
return v___x_1081_;
}
else
{
lean_object* v_i_1082_; lean_object* v_children_1083_; lean_object* v_val_1084_; lean_object* v___x_1085_; 
v_i_1082_ = lean_ctor_get(v_x_1072_, 0);
lean_inc_ref_n(v_i_1082_, 2);
v_children_1083_ = lean_ctor_get(v_x_1072_, 1);
lean_inc_ref_n(v_children_1083_, 2);
lean_dec_ref(v_x_1072_);
v_val_1084_ = lean_ctor_get(v_x_1071_, 0);
lean_inc_n(v_val_1084_, 2);
lean_inc_ref(v_preNode_1069_);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
v___x_1085_ = lean_apply_6(v_preNode_1069_, v_val_1084_, v_i_1082_, v_children_1083_, v___y_1073_, v___y_1074_, lean_box(0));
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; uint8_t v___x_1087_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1085_);
v___x_1087_ = lean_unbox(v_a_1086_);
lean_dec(v_a_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1112_; 
lean_dec_ref(v_preNode_1069_);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1112_ == 0)
{
lean_object* v_unused_1113_; 
v_unused_1113_ = lean_ctor_get(v_x_1071_, 0);
lean_dec(v_unused_1113_);
v___x_1089_ = v_x_1071_;
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v_x_1071_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_box(0);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
v___x_1092_ = lean_apply_7(v_postNode_1070_, v_val_1084_, v_i_1082_, v_children_1083_, v___x_1091_, v___y_1073_, v___y_1074_, lean_box(0));
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1103_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1103_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1103_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v_a_1093_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1100_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
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
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_del_object(v___x_1089_);
v_a_1104_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1092_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1092_);
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
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1114_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1071_, v_i_1082_);
v___x_1115_ = l_Lean_PersistentArray_toList___redArg(v_children_1083_);
v___x_1116_ = lean_box(0);
lean_inc_ref(v_postNode_1070_);
v___x_1117_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1069_, v_postNode_1070_, v___x_1114_, v___x_1115_, v___x_1116_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1117_);
lean_inc(v___y_1074_);
lean_inc_ref(v___y_1073_);
v___x_1119_ = lean_apply_7(v_postNode_1070_, v_val_1084_, v_i_1082_, v_children_1083_, v_a_1118_, v___y_1073_, v___y_1074_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_a_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
v_a_1129_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1119_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1119_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_val_1084_);
lean_dec_ref(v_children_1083_);
lean_dec_ref(v_i_1082_);
lean_dec_ref(v_postNode_1070_);
v_a_1137_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1117_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1117_);
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
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_val_1084_);
lean_dec_ref(v_children_1083_);
lean_dec_ref(v_i_1082_);
lean_dec_ref(v_x_1071_);
lean_dec_ref(v_postNode_1070_);
lean_dec_ref(v_preNode_1069_);
v_a_1145_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1085_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1085_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
default: 
{
lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_x_1071_);
lean_dec_ref(v_postNode_1070_);
lean_dec_ref(v_preNode_1069_);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v_x_1072_, 0);
lean_dec(v_unused_1161_);
v___x_1154_ = v_x_1072_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_dec(v_x_1072_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_box(0);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1162_, lean_object* v_postNode_1163_, lean_object* v___x_1164_, lean_object* v_x_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
if (lean_obj_tag(v_x_1165_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
lean_dec(v___x_1164_);
lean_dec_ref(v_postNode_1163_);
lean_dec_ref(v_preNode_1162_);
v___x_1170_ = l_List_reverse___redArg(v_x_1166_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v_head_1172_; lean_object* v_tail_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1191_; 
v_head_1172_ = lean_ctor_get(v_x_1165_, 0);
v_tail_1173_ = lean_ctor_get(v_x_1165_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_x_1165_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1175_ = v_x_1165_;
v_isShared_1176_ = v_isSharedCheck_1191_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_tail_1173_);
lean_inc(v_head_1172_);
lean_dec(v_x_1165_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1191_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; 
lean_inc(v___x_1164_);
lean_inc_ref(v_postNode_1163_);
lean_inc_ref(v_preNode_1162_);
v___x_1177_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1162_, v_postNode_1163_, v___x_1164_, v_head_1172_, v___y_1167_, v___y_1168_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref(v___x_1177_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_x_1166_);
lean_ctor_set(v___x_1175_, 0, v_a_1178_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1178_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_x_1166_);
v___x_1180_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
v_x_1165_ = v_tail_1173_;
v_x_1166_ = v___x_1180_;
goto _start;
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_del_object(v___x_1175_);
lean_dec(v_tail_1173_);
lean_dec(v_x_1166_);
lean_dec(v___x_1164_);
lean_dec_ref(v_postNode_1163_);
lean_dec_ref(v_preNode_1162_);
v_a_1183_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1177_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1177_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1192_, lean_object* v_postNode_1193_, lean_object* v___x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1192_, v_postNode_1193_, v___x_1194_, v_x_1195_, v_x_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1201_, lean_object* v_postNode_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1201_, v_postNode_1202_, v_x_1203_, v_x_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1209_, lean_object* v_postNode_1210_, lean_object* v_ctx_x3f_1211_, lean_object* v_t_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___f_1216_; lean_object* v___x_1217_; 
v___f_1216_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1216_, 0, v_postNode_1210_);
v___x_1217_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1209_, v___f_1216_, v_ctx_x3f_1211_, v_t_1212_, v___y_1213_, v___y_1214_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1226_);
v___x_1219_ = v___x_1217_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_dec(v___x_1217_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_box(0);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
v_a_1227_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1217_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1217_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1235_, lean_object* v_postNode_1236_, lean_object* v_ctx_x3f_1237_, lean_object* v_t_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1235_, v_postNode_1236_, v_ctx_x3f_1237_, v_t_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1243_, lean_object* v_val_1244_, lean_object* v_val_1245_, lean_object* v_as_1246_, size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_b_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref(v_val_1245_);
lean_dec(v_val_1244_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_b_1249_);
return v___x_1254_;
}
else
{
lean_object* v___x_1255_; lean_object* v___f_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1255_ = lean_box(v___x_1243_);
v___f_1256_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1256_, 0, v___x_1255_);
v___x_1257_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1258_ = lean_box(0);
lean_inc_ref(v_val_1245_);
lean_inc(v_val_1244_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1259_, 0, v_val_1244_);
lean_closure_set(v___f_1259_, 1, v___x_1258_);
lean_closure_set(v___f_1259_, 2, v_val_1245_);
lean_closure_set(v___f_1259_, 3, v___x_1257_);
v_a_1260_ = lean_array_uget_borrowed(v_as_1246_, v_i_1248_);
v___x_1261_ = lean_box(0);
lean_inc(v_a_1260_);
v___x_1262_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1256_, v___f_1259_, v___x_1261_, v_a_1260_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1262_) == 0)
{
size_t v___x_1263_; size_t v___x_1264_; 
lean_dec_ref(v___x_1262_);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1248_, v___x_1263_);
v_i_1248_ = v___x_1264_;
v_b_1249_ = v___x_1258_;
goto _start;
}
else
{
lean_dec_ref(v_val_1245_);
lean_dec(v_val_1244_);
return v___x_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1266_, lean_object* v_val_1267_, lean_object* v_val_1268_, lean_object* v_as_1269_, lean_object* v_sz_1270_, lean_object* v_i_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v___x_23443__boxed_1276_; size_t v_sz_boxed_1277_; size_t v_i_boxed_1278_; lean_object* v_res_1279_; 
v___x_23443__boxed_1276_ = lean_unbox(v___x_1266_);
v_sz_boxed_1277_ = lean_unbox_usize(v_sz_1270_);
lean_dec(v_sz_1270_);
v_i_boxed_1278_ = lean_unbox_usize(v_i_1271_);
lean_dec(v_i_1271_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23443__boxed_1276_, v_val_1267_, v_val_1268_, v_as_1269_, v_sz_boxed_1277_, v_i_boxed_1278_, v_b_1272_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec_ref(v_as_1269_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
if (lean_obj_tag(v_x_1281_) == 0)
{
return v_x_1280_;
}
else
{
lean_object* v_key_1282_; lean_object* v_value_1283_; lean_object* v_tail_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_key_1282_ = lean_ctor_get(v_x_1281_, 0);
v_value_1283_ = lean_ctor_get(v_x_1281_, 1);
v_tail_1284_ = lean_ctor_get(v_x_1281_, 2);
lean_inc(v_value_1283_);
lean_inc(v_key_1282_);
v___x_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1285_, 0, v_key_1282_);
lean_ctor_set(v___x_1285_, 1, v_value_1283_);
v___x_1286_ = lean_array_push(v_x_1280_, v___x_1285_);
v_x_1280_ = v___x_1286_;
v_x_1281_ = v_tail_1284_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1288_, lean_object* v_x_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1288_, v_x_1289_);
lean_dec(v_x_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1291_, size_t v_i_1292_, size_t v_stop_1293_, lean_object* v_b_1294_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_usize_dec_eq(v_i_1292_, v_stop_1293_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; 
v___x_1296_ = lean_array_uget_borrowed(v_as_1291_, v_i_1292_);
v___x_1297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1294_, v___x_1296_);
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1292_, v___x_1298_);
v_i_1292_ = v___x_1299_;
v_b_1294_ = v___x_1297_;
goto _start;
}
else
{
return v_b_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1301_, lean_object* v_i_1302_, lean_object* v_stop_1303_, lean_object* v_b_1304_){
_start:
{
size_t v_i_boxed_1305_; size_t v_stop_boxed_1306_; lean_object* v_res_1307_; 
v_i_boxed_1305_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_stop_boxed_1306_ = lean_unbox_usize(v_stop_1303_);
lean_dec(v_stop_1303_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1301_, v_i_boxed_1305_, v_stop_boxed_1306_, v_b_1304_);
lean_dec_ref(v_as_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_scopes_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_opts_1315_; lean_object* v___x_1316_; 
v___x_1311_ = lean_st_ref_get(v___y_1309_);
v_scopes_1312_ = lean_ctor_get(v___x_1311_, 2);
lean_inc(v_scopes_1312_);
lean_dec(v___x_1311_);
v___x_1313_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1314_ = l_List_head_x21___redArg(v___x_1313_, v_scopes_1312_);
lean_dec(v_scopes_1312_);
v_opts_1315_ = lean_ctor_get(v___x_1314_, 1);
lean_inc_ref(v_opts_1315_);
lean_dec(v___x_1314_);
v___x_1316_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1315_, v___y_1309_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
return v_res_1320_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_unsigned_to_nat(16u);
v___x_1323_ = lean_mk_array(v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
lean_ctor_set(v___x_1326_, 1, v___x_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1402_; 
v___x_1331_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1328_, v___y_1329_);
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1402_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1402_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1337_ = l_Lean_Linter_getLinterValue(v___x_1336_, v_a_1332_);
lean_dec(v_a_1332_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_box(0);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1338_);
v___x_1340_ = v___x_1334_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
uint8_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = 0;
v___x_1343_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1327_, v___x_1342_);
if (lean_obj_tag(v___x_1343_) == 1)
{
lean_object* v_val_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_infoState_1349_; lean_object* v_trees_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; size_t v_sz_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
lean_del_object(v___x_1334_);
v_val_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_val_1344_);
lean_dec_ref(v___x_1343_);
v___x_1345_ = lean_st_ref_get(v___y_1329_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1348_ = lean_st_mk_ref(v___x_1347_);
v_infoState_1349_ = lean_ctor_get(v___x_1345_, 8);
lean_inc_ref(v_infoState_1349_);
lean_dec(v___x_1345_);
v_trees_1350_ = lean_ctor_get(v_infoState_1349_, 2);
lean_inc_ref(v_trees_1350_);
lean_dec_ref(v_infoState_1349_);
v___x_1351_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1350_);
lean_dec_ref(v_trees_1350_);
v___x_1352_ = lean_box(0);
v_sz_1353_ = lean_array_size(v___x_1351_);
v___x_1354_ = ((size_t)0ULL);
lean_inc(v___x_1348_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1337_, v___x_1348_, v_val_1344_, v___x_1351_, v_sz_1353_, v___x_1354_, v___x_1352_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___x_1351_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1356_; lean_object* v___y_1358_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1382_; lean_object* v_size_1388_; lean_object* v_buckets_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
lean_dec_ref(v___x_1355_);
v___x_1356_ = lean_st_ref_get(v___x_1348_);
lean_dec(v___x_1348_);
v_size_1388_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_size_1388_);
v_buckets_1389_ = lean_ctor_get(v___x_1356_, 1);
lean_inc_ref(v_buckets_1389_);
lean_dec(v___x_1356_);
v___x_1390_ = lean_mk_empty_array_with_capacity(v_size_1388_);
lean_dec(v_size_1388_);
v___x_1391_ = lean_array_get_size(v_buckets_1389_);
v___x_1392_ = lean_nat_dec_lt(v___x_1346_, v___x_1391_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v_buckets_1389_);
v___y_1382_ = v___x_1390_;
goto v___jp_1381_;
}
else
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_nat_dec_le(v___x_1391_, v___x_1391_);
if (v___x_1393_ == 0)
{
if (v___x_1392_ == 0)
{
lean_dec_ref(v_buckets_1389_);
v___y_1382_ = v___x_1390_;
goto v___jp_1381_;
}
else
{
size_t v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = lean_usize_of_nat(v___x_1391_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1389_, v___x_1354_, v___x_1394_, v___x_1390_);
lean_dec_ref(v_buckets_1389_);
v___y_1382_ = v___x_1395_;
goto v___jp_1381_;
}
}
else
{
size_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_usize_of_nat(v___x_1391_);
v___x_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1389_, v___x_1354_, v___x_1396_, v___x_1390_);
lean_dec_ref(v_buckets_1389_);
v___y_1382_ = v___x_1397_;
goto v___jp_1381_;
}
}
v___jp_1357_:
{
size_t v_sz_1359_; lean_object* v___x_1360_; 
v_sz_1359_ = lean_array_size(v___y_1358_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1358_, v_sz_1359_, v___x_1354_, v___x_1352_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1358_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v___x_1360_, 0);
lean_dec(v_unused_1368_);
v___x_1362_ = v___x_1360_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_dec(v___x_1360_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1352_);
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1352_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
else
{
return v___x_1360_;
}
}
v___jp_1369_:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1370_, v___y_1372_, v___y_1371_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec(v___y_1370_);
v___y_1358_ = v___x_1374_;
goto v___jp_1357_;
}
v___jp_1375_:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_nat_dec_le(v___y_1379_, v___y_1377_);
if (v___x_1380_ == 0)
{
lean_dec(v___y_1377_);
lean_inc(v___y_1379_);
v___y_1370_ = v___y_1376_;
v___y_1371_ = v___y_1379_;
v___y_1372_ = v___y_1378_;
v___y_1373_ = v___y_1379_;
goto v___jp_1369_;
}
else
{
v___y_1370_ = v___y_1376_;
v___y_1371_ = v___y_1379_;
v___y_1372_ = v___y_1378_;
v___y_1373_ = v___y_1377_;
goto v___jp_1369_;
}
}
v___jp_1381_:
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = lean_array_get_size(v___y_1382_);
v___x_1384_ = lean_nat_dec_eq(v___x_1383_, v___x_1346_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1385_ = lean_unsigned_to_nat(1u);
v___x_1386_ = lean_nat_sub(v___x_1383_, v___x_1385_);
v___x_1387_ = lean_nat_dec_le(v___x_1346_, v___x_1386_);
if (v___x_1387_ == 0)
{
lean_inc(v___x_1386_);
v___y_1376_ = v___x_1383_;
v___y_1377_ = v___x_1386_;
v___y_1378_ = v___y_1382_;
v___y_1379_ = v___x_1386_;
goto v___jp_1375_;
}
else
{
v___y_1376_ = v___x_1383_;
v___y_1377_ = v___x_1386_;
v___y_1378_ = v___y_1382_;
v___y_1379_ = v___x_1346_;
goto v___jp_1375_;
}
}
else
{
v___y_1358_ = v___y_1382_;
goto v___jp_1357_;
}
}
}
else
{
lean_dec(v___x_1348_);
return v___x_1355_;
}
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_dec(v___x_1343_);
v___x_1398_ = lean_box(0);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1398_);
v___x_1400_ = v___x_1334_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v_cmdStx_1403_);
return v_res_1407_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1417_, lean_object* v_m_1418_, lean_object* v_a_1419_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1418_, v_a_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1421_, lean_object* v_m_1422_, lean_object* v_a_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1421_, v_m_1422_, v_a_1423_);
lean_dec_ref(v_a_1423_);
lean_dec_ref(v_m_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_, lean_object* v_b_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1427_, v_a_1428_, v_b_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1431_, lean_object* v_val_1432_, lean_object* v_info_1433_, lean_object* v___x_1434_, lean_object* v_val_1435_, uint8_t v___x_1436_, lean_object* v_as_1437_, lean_object* v_as_x27_1438_, lean_object* v_b_1439_, lean_object* v_a_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1431_, v_val_1432_, v_info_1433_, v___x_1434_, v_val_1435_, v___x_1436_, v_as_x27_1438_, v_b_1439_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1445_, lean_object* v_val_1446_, lean_object* v_info_1447_, lean_object* v___x_1448_, lean_object* v_val_1449_, lean_object* v___x_1450_, lean_object* v_as_1451_, lean_object* v_as_x27_1452_, lean_object* v_b_1453_, lean_object* v_a_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v___x_23735__boxed_1458_; lean_object* v_res_1459_; 
v___x_23735__boxed_1458_ = lean_unbox(v___x_1450_);
v_res_1459_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1445_, v_val_1446_, v_info_1447_, v___x_1448_, v_val_1449_, v___x_23735__boxed_1458_, v_as_1451_, v_as_x27_1452_, v_b_1453_, v_a_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v_as_x27_1452_);
lean_dec(v_as_1451_);
lean_dec_ref(v_info_1447_);
lean_dec(v_val_1446_);
lean_dec_ref(v_str_1445_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1460_, lean_object* v_as_1461_, lean_object* v_lo_1462_, lean_object* v_hi_1463_, lean_object* v_w_1464_, lean_object* v_hlo_1465_, lean_object* v_hhi_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1460_, v_as_1461_, v_lo_1462_, v_hi_1463_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1468_, lean_object* v_as_1469_, lean_object* v_lo_1470_, lean_object* v_hi_1471_, lean_object* v_w_1472_, lean_object* v_hlo_1473_, lean_object* v_hhi_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1468_, v_as_1469_, v_lo_1470_, v_hi_1471_, v_w_1472_, v_hlo_1473_, v_hhi_1474_);
lean_dec(v_hi_1471_);
lean_dec(v_n_1468_);
return v_res_1475_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1477_, v_x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1480_, lean_object* v_a_1481_, lean_object* v_x_1482_){
_start:
{
uint8_t v_res_1483_; lean_object* v_r_1484_; 
v_res_1483_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1480_, v_a_1481_, v_x_1482_);
lean_dec(v_x_1482_);
lean_dec_ref(v_a_1481_);
v_r_1484_ = lean_box(v_res_1483_);
return v_r_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1485_, lean_object* v_data_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1488_, lean_object* v_a_1489_, lean_object* v_b_1490_, lean_object* v_x_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1489_, v_b_1490_, v_x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1493_, lean_object* v_msg_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1494_, v___y_1495_, v___y_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1499_, v_msg_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1505_, lean_object* v_preNode_1506_, lean_object* v_postNode_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1506_, v_postNode_1507_, v_x_1508_, v_x_1509_, v___y_1510_, v___y_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1514_, lean_object* v_preNode_1515_, lean_object* v_postNode_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1514_, v_preNode_1515_, v_postNode_1516_, v_x_1517_, v_x_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object* v_n_1523_, lean_object* v_lo_1524_, lean_object* v_hi_1525_, lean_object* v_hhi_1526_, lean_object* v_pivot_1527_, lean_object* v_as_1528_, lean_object* v_i_1529_, lean_object* v_k_1530_, lean_object* v_ilo_1531_, lean_object* v_ik_1532_, lean_object* v_w_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1525_, v_pivot_1527_, v_as_1528_, v_i_1529_, v_k_1530_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object* v_n_1535_, lean_object* v_lo_1536_, lean_object* v_hi_1537_, lean_object* v_hhi_1538_, lean_object* v_pivot_1539_, lean_object* v_as_1540_, lean_object* v_i_1541_, lean_object* v_k_1542_, lean_object* v_ilo_1543_, lean_object* v_ik_1544_, lean_object* v_w_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_1535_, v_lo_1536_, v_hi_1537_, v_hhi_1538_, v_pivot_1539_, v_as_1540_, v_i_1541_, v_k_1542_, v_ilo_1543_, v_ik_1544_, v_w_1545_);
lean_dec_ref(v_pivot_1539_);
lean_dec(v_hi_1537_);
lean_dec(v_lo_1536_);
lean_dec(v_n_1535_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1547_, lean_object* v_i_1548_, lean_object* v_source_1549_, lean_object* v_target_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1548_, v_source_1549_, v_target_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1552_, lean_object* v_preNode_1553_, lean_object* v_postNode_1554_, lean_object* v___x_1555_, lean_object* v_x_1556_, lean_object* v_x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1553_, v_postNode_1554_, v___x_1555_, v_x_1556_, v_x_1557_, v___y_1558_, v___y_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1562_, lean_object* v_preNode_1563_, lean_object* v_postNode_1564_, lean_object* v___x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1562_, v_preNode_1563_, v_postNode_1564_, v___x_1565_, v_x_1566_, v_x_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1572_, v___y_1574_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1582_, lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1583_, v_x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1588_ = l_Lean_Elab_Command_addLinter(v___x_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1590_;
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
res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
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
