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
uint8_t v___y_21684__boxed_219_; uint8_t v_suppressElabErrors_boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___y_21684__boxed_219_ = lean_unbox(v___y_216_);
v_suppressElabErrors_boxed_220_ = lean_unbox(v_suppressElabErrors_217_);
v_res_221_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21684__boxed_219_, v_suppressElabErrors_boxed_220_, v_x_218_);
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
lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; uint8_t v___y_287_; lean_object* v___y_288_; uint8_t v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; uint8_t v___y_347_; lean_object* v___y_348_; uint8_t v___y_349_; uint8_t v___y_350_; lean_object* v___y_351_; uint8_t v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; uint8_t v___y_383_; uint8_t v___y_384_; uint8_t v___y_385_; uint8_t v___x_400_; uint8_t v___y_402_; uint8_t v___y_403_; uint8_t v___y_404_; uint8_t v___y_406_; uint8_t v___x_418_; 
v___x_400_ = 2;
v___x_418_ = l_Lean_instBEqMessageSeverity_beq(v_severity_278_, v___x_400_);
if (v___x_418_ == 0)
{
v___y_406_ = v___x_418_;
goto v___jp_405_;
}
else
{
uint8_t v___x_419_; 
lean_inc_ref(v_msgData_277_);
v___x_419_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_277_);
v___y_406_ = v___x_419_;
goto v___jp_405_;
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
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_329_; 
v_a_295_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_329_ == 0)
{
v___x_297_ = v___x_294_;
v_isShared_298_ = v_isSharedCheck_329_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_329_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v_currNamespace_300_; lean_object* v_openDecls_301_; lean_object* v_env_302_; lean_object* v_messages_303_; lean_object* v_scopes_304_; lean_object* v_usedQuotCtxts_305_; lean_object* v_nextMacroScope_306_; lean_object* v_maxRecDepth_307_; lean_object* v_ngen_308_; lean_object* v_auxDeclNGen_309_; lean_object* v_infoState_310_; lean_object* v_traceState_311_; lean_object* v_snapshotTasks_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_328_; 
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
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_328_ == 0)
{
v___x_314_ = v___x_299_;
v_isShared_315_ = v_isSharedCheck_328_;
goto v_resetjp_313_;
}
else
{
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
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_328_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_currNamespace_300_);
lean_ctor_set(v___x_316_, 1, v_openDecls_301_);
v___x_317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___y_286_);
lean_inc_ref(v___y_290_);
lean_inc_ref(v___y_284_);
v___x_318_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_318_, 0, v___y_284_);
lean_ctor_set(v___x_318_, 1, v___y_285_);
lean_ctor_set(v___x_318_, 2, v___y_288_);
lean_ctor_set(v___x_318_, 3, v___y_290_);
lean_ctor_set(v___x_318_, 4, v___x_317_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*5, v___y_289_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*5 + 1, v___y_287_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*5 + 2, v_isSilent_279_);
v___x_319_ = l_Lean_MessageLog_add(v___x_318_, v_messages_303_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_319_);
v___x_321_ = v___x_314_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_env_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_scopes_304_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_usedQuotCtxts_305_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_nextMacroScope_306_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_maxRecDepth_307_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_ngen_308_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_auxDeclNGen_309_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_327_, 9, v_traceState_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 10, v_snapshotTasks_312_);
v___x_321_ = v_reuseFailAlloc_327_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_st_ref_set(v___y_291_, v___x_321_);
v___x_323_ = lean_box(0);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_323_);
v___x_325_ = v___x_297_;
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
}
}
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_a_293_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_286_);
lean_dec_ref(v___y_285_);
v_a_330_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_294_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_294_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v___y_288_);
lean_dec_ref(v___y_286_);
lean_dec_ref(v___y_285_);
v_a_338_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_292_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_292_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
v___jp_346_:
{
lean_object* v_fileName_352_; lean_object* v_fileMap_353_; uint8_t v_suppressElabErrors_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_373_; 
v_fileName_352_ = lean_ctor_get(v___y_280_, 0);
v_fileMap_353_ = lean_ctor_get(v___y_280_, 1);
v_suppressElabErrors_354_ = lean_ctor_get_uint8(v___y_280_, sizeof(void*)*10);
v___x_355_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_277_);
v___x_356_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_355_, v___y_281_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_373_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_373_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
lean_inc_ref_n(v_fileMap_353_, 2);
v___x_361_ = l_Lean_FileMap_toPosition(v_fileMap_353_, v___y_348_);
lean_dec(v___y_348_);
v___x_362_ = l_Lean_FileMap_toPosition(v_fileMap_353_, v___y_351_);
lean_dec(v___y_351_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_354_ == 0)
{
lean_del_object(v___x_359_);
v___y_284_ = v_fileName_352_;
v___y_285_ = v___x_361_;
v___y_286_ = v_a_357_;
v___y_287_ = v___y_349_;
v___y_288_ = v___x_363_;
v___y_289_ = v___y_350_;
v___y_290_ = v___x_364_;
v___y_291_ = v___y_281_;
goto v___jp_283_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___f_367_; uint8_t v___x_368_; 
v___x_365_ = lean_box(v___y_347_);
v___x_366_ = lean_box(v_suppressElabErrors_354_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed), 3, 2);
lean_closure_set(v___f_367_, 0, v___x_365_);
lean_closure_set(v___f_367_, 1, v___x_366_);
lean_inc(v_a_357_);
v___x_368_ = l_Lean_MessageData_hasTag(v___f_367_, v_a_357_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v___x_363_);
lean_dec_ref(v___x_361_);
lean_dec(v_a_357_);
v___x_369_ = lean_box(0);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_369_);
v___x_371_ = v___x_359_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
else
{
lean_del_object(v___x_359_);
v___y_284_ = v_fileName_352_;
v___y_285_ = v___x_361_;
v___y_286_ = v_a_357_;
v___y_287_ = v___y_349_;
v___y_288_ = v___x_363_;
v___y_289_ = v___y_350_;
v___y_290_ = v___x_364_;
v___y_291_ = v___y_281_;
goto v___jp_283_;
}
}
}
}
v___jp_374_:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Syntax_getTailPos_x3f(v___y_376_, v___y_378_);
lean_dec(v___y_376_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_inc(v___y_379_);
v___y_347_ = v___y_375_;
v___y_348_ = v___y_379_;
v___y_349_ = v___y_377_;
v___y_350_ = v___y_378_;
v___y_351_ = v___y_379_;
goto v___jp_346_;
}
else
{
lean_object* v_val_381_; 
v_val_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_val_381_);
lean_dec_ref(v___x_380_);
v___y_347_ = v___y_375_;
v___y_348_ = v___y_379_;
v___y_349_ = v___y_377_;
v___y_350_ = v___y_378_;
v___y_351_ = v_val_381_;
goto v___jp_346_;
}
}
v___jp_382_:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Elab_Command_getRef___redArg(v___y_280_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v_ref_388_; lean_object* v___x_389_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_a_387_);
lean_dec_ref(v___x_386_);
v_ref_388_ = l_Lean_replaceRef(v_ref_276_, v_a_387_);
lean_dec(v_a_387_);
v___x_389_ = l_Lean_Syntax_getPos_x3f(v_ref_388_, v___y_384_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___y_375_ = v___y_383_;
v___y_376_ = v_ref_388_;
v___y_377_ = v___y_385_;
v___y_378_ = v___y_384_;
v___y_379_ = v___x_390_;
goto v___jp_374_;
}
else
{
lean_object* v_val_391_; 
v_val_391_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_391_);
lean_dec_ref(v___x_389_);
v___y_375_ = v___y_383_;
v___y_376_ = v_ref_388_;
v___y_377_ = v___y_385_;
v___y_378_ = v___y_384_;
v___y_379_ = v_val_391_;
goto v___jp_374_;
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v_msgData_277_);
v_a_392_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_386_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_386_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
v___jp_401_:
{
if (v___y_404_ == 0)
{
v___y_383_ = v___y_402_;
v___y_384_ = v___y_403_;
v___y_385_ = v_severity_278_;
goto v___jp_382_;
}
else
{
v___y_383_ = v___y_402_;
v___y_384_ = v___y_403_;
v___y_385_ = v___x_400_;
goto v___jp_382_;
}
}
v___jp_405_:
{
if (v___y_406_ == 0)
{
lean_object* v___x_407_; lean_object* v_scopes_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_opts_411_; uint8_t v___x_412_; uint8_t v___x_413_; 
v___x_407_ = lean_st_ref_get(v___y_281_);
v_scopes_408_ = lean_ctor_get(v___x_407_, 2);
lean_inc(v_scopes_408_);
lean_dec(v___x_407_);
v___x_409_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_410_ = l_List_head_x21___redArg(v___x_409_, v_scopes_408_);
lean_dec(v_scopes_408_);
v_opts_411_ = lean_ctor_get(v___x_410_, 1);
lean_inc_ref(v_opts_411_);
lean_dec(v___x_410_);
v___x_412_ = 1;
v___x_413_ = l_Lean_instBEqMessageSeverity_beq(v_severity_278_, v___x_412_);
if (v___x_413_ == 0)
{
lean_dec_ref(v_opts_411_);
v___y_402_ = v___y_406_;
v___y_403_ = v___y_406_;
v___y_404_ = v___x_413_;
goto v___jp_401_;
}
else
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = l_Lean_warningAsError;
v___x_415_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_411_, v___x_414_);
lean_dec_ref(v_opts_411_);
v___y_402_ = v___y_406_;
v___y_403_ = v___y_406_;
v___y_404_ = v___x_415_;
goto v___jp_401_;
}
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref(v_msgData_277_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object* v_ref_420_, lean_object* v_msgData_421_, lean_object* v_severity_422_, lean_object* v_isSilent_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v_severity_boxed_427_; uint8_t v_isSilent_boxed_428_; lean_object* v_res_429_; 
v_severity_boxed_427_ = lean_unbox(v_severity_422_);
v_isSilent_boxed_428_ = lean_unbox(v_isSilent_423_);
v_res_429_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_420_, v_msgData_421_, v_severity_boxed_427_, v_isSilent_boxed_428_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_ref_420_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object* v_ref_430_, lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = 1;
v___x_436_ = 0;
v___x_437_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_430_, v_msgData_431_, v___x_435_, v___x_436_, v___y_432_, v___y_433_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object* v_ref_438_, lean_object* v_msgData_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_438_, v_msgData_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v_ref_438_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* v_linterOption_450_, lean_object* v_stx_451_, lean_object* v_msg_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_name_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_471_; 
v_name_456_ = lean_ctor_get(v_linterOption_450_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_linterOption_450_);
if (v_isSharedCheck_471_ == 0)
{
lean_object* v_unused_472_; 
v_unused_472_ = lean_ctor_get(v_linterOption_450_, 1);
lean_dec(v_unused_472_);
v___x_458_ = v_linterOption_450_;
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_name_456_);
lean_dec(v_linterOption_450_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_471_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_460_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
lean_inc(v_name_456_);
v___x_461_ = l_Lean_MessageData_ofName(v_name_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 7);
lean_ctor_set(v___x_458_, 1, v___x_461_);
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_463_ = v___x_458_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_470_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_disable_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_464_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v_disable_466_ = l_Lean_MessageData_note(v___x_465_);
v___x_467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_467_, 0, v_msg_452_);
lean_ctor_set(v___x_467_, 1, v_disable_466_);
v___x_468_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_468_, 0, v_name_456_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_451_, v___x_468_, v___y_453_, v___y_454_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_473_, lean_object* v_stx_474_, lean_object* v_msg_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_473_, v_stx_474_, v_msg_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v_stx_474_);
return v_res_479_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_498_, size_t v_sz_499_, size_t v_i_500_, lean_object* v_b_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_lt(v_i_500_, v_sz_499_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v_b_501_);
return v___x_506_;
}
else
{
lean_object* v_a_507_; lean_object* v_snd_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_553_; 
v_a_507_ = lean_array_uget(v_as_498_, v_i_500_);
v_snd_508_ = lean_ctor_get(v_a_507_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_507_);
if (v_isSharedCheck_553_ == 0)
{
lean_object* v_unused_554_; 
v_unused_554_ = lean_ctor_get(v_a_507_, 0);
lean_dec(v_unused_554_);
v___x_510_ = v_a_507_;
v_isShared_511_ = v_isSharedCheck_553_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_snd_508_);
lean_dec(v_a_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_553_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v_snd_512_; lean_object* v_fst_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_552_; 
v_snd_512_ = lean_ctor_get(v_snd_508_, 1);
v_fst_513_ = lean_ctor_get(v_snd_508_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_snd_508_);
if (v_isSharedCheck_552_ == 0)
{
v___x_515_ = v_snd_508_;
v_isShared_516_ = v_isSharedCheck_552_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_snd_512_);
lean_inc(v_fst_513_);
lean_dec(v_snd_508_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_552_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_fst_517_; lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_551_; 
v_fst_517_ = lean_ctor_get(v_snd_512_, 0);
v_snd_518_ = lean_ctor_get(v_snd_512_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_snd_512_);
if (v_isSharedCheck_551_ == 0)
{
v___x_520_ = v_snd_512_;
v_isShared_521_ = v_isSharedCheck_551_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_inc(v_fst_517_);
lean_dec(v_snd_512_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_551_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_522_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_523_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_524_ = l_Lean_MessageData_ofName(v_fst_517_);
lean_inc_ref(v___x_524_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 7);
lean_ctor_set(v___x_520_, 1, v___x_524_);
lean_ctor_set(v___x_520_, 0, v___x_523_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_550_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_527_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_516_ == 0)
{
lean_ctor_set_tag(v___x_515_, 7);
lean_ctor_set(v___x_515_, 1, v___x_527_);
lean_ctor_set(v___x_515_, 0, v___x_526_);
v___x_529_ = v___x_515_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v___x_527_);
v___x_529_ = v_reuseFailAlloc_549_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = l_Lean_MessageData_ofName(v_snd_518_);
lean_inc_ref(v___x_530_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 7);
lean_ctor_set(v___x_510_, 1, v___x_530_);
lean_ctor_set(v___x_510_, 0, v___x_529_);
v___x_532_ = v___x_510_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_548_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_524_);
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v___x_530_);
v___x_540_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_534_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_522_, v_fst_513_, v___x_542_, v___y_502_, v___y_503_);
lean_dec(v_fst_513_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; size_t v___x_545_; size_t v___x_546_; 
lean_dec_ref(v___x_543_);
v___x_544_ = lean_box(0);
v___x_545_ = ((size_t)1ULL);
v___x_546_ = lean_usize_add(v_i_500_, v___x_545_);
v_i_500_ = v___x_546_;
v_b_501_ = v___x_544_;
goto _start;
}
else
{
return v___x_543_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_555_, lean_object* v_sz_556_, lean_object* v_i_557_, lean_object* v_b_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
size_t v_sz_boxed_562_; size_t v_i_boxed_563_; lean_object* v_res_564_; 
v_sz_boxed_562_ = lean_unbox_usize(v_sz_556_);
lean_dec(v_sz_556_);
v_i_boxed_563_ = lean_unbox_usize(v_i_557_);
lean_dec(v_i_557_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_555_, v_sz_boxed_562_, v_i_boxed_563_, v_b_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v_as_555_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_box(v___x_565_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_22296__boxed_581_; lean_object* v_res_582_; 
v___x_22296__boxed_581_ = lean_unbox(v___x_574_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22296__boxed_581_, v_x_575_, v_x_576_, v_x_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec_ref(v_x_577_);
lean_dec_ref(v_x_576_);
lean_dec_ref(v_x_575_);
return v_res_582_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
uint8_t v___x_585_; 
v___x_585_ = 0;
return v___x_585_;
}
else
{
lean_object* v_key_586_; lean_object* v_tail_587_; uint8_t v___x_588_; 
v_key_586_ = lean_ctor_get(v_x_584_, 0);
v_tail_587_ = lean_ctor_get(v_x_584_, 2);
v___x_588_ = l_Lean_Syntax_instBEqRange_beq(v_key_586_, v_a_583_);
if (v___x_588_ == 0)
{
v_x_584_ = v_tail_587_;
goto _start;
}
else
{
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_590_, lean_object* v_x_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_590_, v_x_591_);
lean_dec(v_x_591_);
lean_dec_ref(v_a_590_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_buckets_596_; lean_object* v___x_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v_fold_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; size_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_buckets_596_ = lean_ctor_get(v_m_594_, 1);
v___x_597_ = lean_array_get_size(v_buckets_596_);
v___x_598_ = l_Lean_Syntax_instHashableRange_hash(v_a_595_);
v___x_599_ = 32ULL;
v___x_600_ = lean_uint64_shift_right(v___x_598_, v___x_599_);
v_fold_601_ = lean_uint64_xor(v___x_598_, v___x_600_);
v___x_602_ = 16ULL;
v___x_603_ = lean_uint64_shift_right(v_fold_601_, v___x_602_);
v___x_604_ = lean_uint64_xor(v_fold_601_, v___x_603_);
v___x_605_ = lean_uint64_to_usize(v___x_604_);
v___x_606_ = lean_usize_of_nat(v___x_597_);
v___x_607_ = ((size_t)1ULL);
v___x_608_ = lean_usize_sub(v___x_606_, v___x_607_);
v___x_609_ = lean_usize_land(v___x_605_, v___x_608_);
v___x_610_ = lean_array_uget_borrowed(v_buckets_596_, v___x_609_);
v___x_611_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_595_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_612_, lean_object* v_a_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_612_, v_a_613_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_m_612_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_616_, lean_object* v_b_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_dec(v_b_617_);
lean_dec_ref(v_a_616_);
return v_x_618_;
}
else
{
lean_object* v_key_619_; lean_object* v_value_620_; lean_object* v_tail_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_633_; 
v_key_619_ = lean_ctor_get(v_x_618_, 0);
v_value_620_ = lean_ctor_get(v_x_618_, 1);
v_tail_621_ = lean_ctor_get(v_x_618_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_633_ == 0)
{
v___x_623_ = v_x_618_;
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_tail_621_);
lean_inc(v_value_620_);
lean_inc(v_key_619_);
lean_dec(v_x_618_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_633_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_Syntax_instBEqRange_beq(v_key_619_, v_a_616_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_616_, v_b_617_, v_tail_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 2, v___x_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_key_619_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_value_620_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
lean_dec(v_value_620_);
lean_dec(v_key_619_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 1, v_b_617_);
lean_ctor_set(v___x_623_, 0, v_a_616_);
v___x_631_ = v___x_623_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_b_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_tail_621_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_634_, lean_object* v_x_635_){
_start:
{
if (lean_obj_tag(v_x_635_) == 0)
{
return v_x_634_;
}
else
{
lean_object* v_key_636_; lean_object* v_value_637_; lean_object* v_tail_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_661_; 
v_key_636_ = lean_ctor_get(v_x_635_, 0);
v_value_637_ = lean_ctor_get(v_x_635_, 1);
v_tail_638_ = lean_ctor_get(v_x_635_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_635_);
if (v_isSharedCheck_661_ == 0)
{
v___x_640_ = v_x_635_;
v_isShared_641_ = v_isSharedCheck_661_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_tail_638_);
lean_inc(v_value_637_);
lean_inc(v_key_636_);
lean_dec(v_x_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_661_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v_fold_646_; uint64_t v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_642_ = lean_array_get_size(v_x_634_);
v___x_643_ = l_Lean_Syntax_instHashableRange_hash(v_key_636_);
v___x_644_ = 32ULL;
v___x_645_ = lean_uint64_shift_right(v___x_643_, v___x_644_);
v_fold_646_ = lean_uint64_xor(v___x_643_, v___x_645_);
v___x_647_ = 16ULL;
v___x_648_ = lean_uint64_shift_right(v_fold_646_, v___x_647_);
v___x_649_ = lean_uint64_xor(v_fold_646_, v___x_648_);
v___x_650_ = lean_uint64_to_usize(v___x_649_);
v___x_651_ = lean_usize_of_nat(v___x_642_);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_sub(v___x_651_, v___x_652_);
v___x_654_ = lean_usize_land(v___x_650_, v___x_653_);
v___x_655_ = lean_array_uget_borrowed(v_x_634_, v___x_654_);
lean_inc(v___x_655_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 2, v___x_655_);
v___x_657_ = v___x_640_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_key_636_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_value_637_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v___x_655_);
v___x_657_ = v_reuseFailAlloc_660_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_array_uset(v_x_634_, v___x_654_, v___x_657_);
v_x_634_ = v___x_658_;
v_x_635_ = v_tail_638_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_662_, lean_object* v_source_663_, lean_object* v_target_664_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_array_get_size(v_source_663_);
v___x_666_ = lean_nat_dec_lt(v_i_662_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec_ref(v_source_663_);
lean_dec(v_i_662_);
return v_target_664_;
}
else
{
lean_object* v_es_667_; lean_object* v___x_668_; lean_object* v_source_669_; lean_object* v_target_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_es_667_ = lean_array_fget(v_source_663_, v_i_662_);
v___x_668_ = lean_box(0);
v_source_669_ = lean_array_fset(v_source_663_, v_i_662_, v___x_668_);
v_target_670_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_664_, v_es_667_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_i_662_, v___x_671_);
lean_dec(v_i_662_);
v_i_662_ = v___x_672_;
v_source_663_ = v_source_669_;
v_target_664_ = v_target_670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_nbuckets_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = lean_array_get_size(v_data_674_);
v___x_676_ = lean_unsigned_to_nat(2u);
v_nbuckets_677_ = lean_nat_mul(v___x_675_, v___x_676_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_box(0);
v___x_680_ = lean_mk_array(v_nbuckets_677_, v___x_679_);
v___x_681_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_678_, v_data_674_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_682_, lean_object* v_a_683_, lean_object* v_b_684_){
_start:
{
lean_object* v_size_685_; lean_object* v_buckets_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_729_; 
v_size_685_ = lean_ctor_get(v_m_682_, 0);
v_buckets_686_ = lean_ctor_get(v_m_682_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_m_682_);
if (v_isSharedCheck_729_ == 0)
{
v___x_688_ = v_m_682_;
v_isShared_689_ = v_isSharedCheck_729_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_buckets_686_);
lean_inc(v_size_685_);
lean_dec(v_m_682_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_729_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; uint64_t v___x_691_; uint64_t v___x_692_; uint64_t v___x_693_; uint64_t v_fold_694_; uint64_t v___x_695_; uint64_t v___x_696_; uint64_t v___x_697_; size_t v___x_698_; size_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v_bkt_703_; uint8_t v___x_704_; 
v___x_690_ = lean_array_get_size(v_buckets_686_);
v___x_691_ = l_Lean_Syntax_instHashableRange_hash(v_a_683_);
v___x_692_ = 32ULL;
v___x_693_ = lean_uint64_shift_right(v___x_691_, v___x_692_);
v_fold_694_ = lean_uint64_xor(v___x_691_, v___x_693_);
v___x_695_ = 16ULL;
v___x_696_ = lean_uint64_shift_right(v_fold_694_, v___x_695_);
v___x_697_ = lean_uint64_xor(v_fold_694_, v___x_696_);
v___x_698_ = lean_uint64_to_usize(v___x_697_);
v___x_699_ = lean_usize_of_nat(v___x_690_);
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_sub(v___x_699_, v___x_700_);
v___x_702_ = lean_usize_land(v___x_698_, v___x_701_);
v_bkt_703_ = lean_array_uget_borrowed(v_buckets_686_, v___x_702_);
v___x_704_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_683_, v_bkt_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v_size_x27_706_; lean_object* v___x_707_; lean_object* v_buckets_x27_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_705_ = lean_unsigned_to_nat(1u);
v_size_x27_706_ = lean_nat_add(v_size_685_, v___x_705_);
lean_dec(v_size_685_);
lean_inc(v_bkt_703_);
v___x_707_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_707_, 0, v_a_683_);
lean_ctor_set(v___x_707_, 1, v_b_684_);
lean_ctor_set(v___x_707_, 2, v_bkt_703_);
v_buckets_x27_708_ = lean_array_uset(v_buckets_686_, v___x_702_, v___x_707_);
v___x_709_ = lean_unsigned_to_nat(4u);
v___x_710_ = lean_nat_mul(v_size_x27_706_, v___x_709_);
v___x_711_ = lean_unsigned_to_nat(3u);
v___x_712_ = lean_nat_div(v___x_710_, v___x_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_array_get_size(v_buckets_x27_708_);
v___x_714_ = lean_nat_dec_le(v___x_712_, v___x_713_);
lean_dec(v___x_712_);
if (v___x_714_ == 0)
{
lean_object* v_val_715_; lean_object* v___x_717_; 
v_val_715_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_708_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_val_715_);
lean_ctor_set(v___x_688_, 0, v_size_x27_706_);
v___x_717_ = v___x_688_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_size_x27_706_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_val_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v___x_720_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_buckets_x27_708_);
lean_ctor_set(v___x_688_, 0, v_size_x27_706_);
v___x_720_ = v___x_688_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_size_x27_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_buckets_x27_708_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
lean_object* v___x_722_; lean_object* v_buckets_x27_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
lean_inc(v_bkt_703_);
v___x_722_ = lean_box(0);
v_buckets_x27_723_ = lean_array_uset(v_buckets_686_, v___x_702_, v___x_722_);
v___x_724_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_683_, v_b_684_, v_bkt_703_);
v___x_725_ = lean_array_uset(v_buckets_x27_723_, v___x_702_, v___x_724_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_725_);
v___x_727_ = v___x_688_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_size_685_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_730_, lean_object* v_val_731_, lean_object* v_info_732_, lean_object* v___x_733_, lean_object* v_val_734_, uint8_t v___x_735_, lean_object* v_as_x27_736_, lean_object* v_b_737_, lean_object* v___y_738_){
_start:
{
if (lean_obj_tag(v_as_x27_736_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v_val_734_);
lean_dec(v___x_733_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_b_737_);
return v___x_740_;
}
else
{
lean_object* v_head_741_; lean_object* v_tail_742_; lean_object* v___x_743_; lean_object* v_env_744_; lean_object* v___x_745_; lean_object* v___x_758_; 
v_head_741_ = lean_ctor_get(v_as_x27_736_, 0);
v_tail_742_ = lean_ctor_get(v_as_x27_736_, 1);
v___x_743_ = lean_st_ref_get(v___y_738_);
v_env_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_env_744_);
lean_dec(v___x_743_);
v___x_745_ = lean_box(0);
lean_inc(v_head_741_);
v___x_758_ = l_Lean_Environment_find_x3f(v_env_744_, v_head_741_, v___x_735_);
if (lean_obj_tag(v___x_758_) == 1)
{
lean_object* v_val_759_; 
v_val_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_759_);
lean_dec_ref(v___x_758_);
if (lean_obj_tag(v_val_759_) == 6)
{
lean_object* v_val_760_; lean_object* v_numFields_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_val_760_ = lean_ctor_get(v_val_759_, 0);
lean_inc_ref(v_val_760_);
lean_dec_ref(v_val_759_);
v_numFields_761_ = lean_ctor_get(v_val_760_, 4);
lean_inc(v_numFields_761_);
lean_dec_ref(v_val_760_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_nat_dec_lt(v___x_762_, v_numFields_761_);
lean_dec(v_numFields_761_);
if (v___x_763_ == 0)
{
goto v___jp_746_;
}
else
{
v_as_x27_736_ = v_tail_742_;
v_b_737_ = v___x_745_;
goto _start;
}
}
else
{
lean_dec(v_val_759_);
goto v___jp_746_;
}
}
else
{
lean_dec(v___x_758_);
goto v___jp_746_;
}
v___jp_746_:
{
if (lean_obj_tag(v_head_741_) == 1)
{
lean_object* v_str_747_; uint8_t v___x_748_; 
v_str_747_ = lean_ctor_get(v_head_741_, 1);
v___x_748_ = lean_string_dec_eq(v_str_747_, v_str_730_);
if (v___x_748_ == 0)
{
v_as_x27_736_ = v_tail_742_;
v_b_737_ = v___x_745_;
goto _start;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_750_ = lean_st_ref_take(v_val_731_);
v___x_751_ = l_Lean_Elab_Info_stx(v_info_732_);
lean_inc_ref(v_head_741_);
lean_inc(v___x_733_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_733_);
lean_ctor_set(v___x_752_, 1, v_head_741_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_inc_ref(v_val_734_);
v___x_754_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_750_, v_val_734_, v___x_753_);
v___x_755_ = lean_st_ref_set(v_val_731_, v___x_754_);
v_as_x27_736_ = v_tail_742_;
v_b_737_ = v___x_745_;
goto _start;
}
}
else
{
v_as_x27_736_ = v_tail_742_;
v_b_737_ = v___x_745_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_765_, lean_object* v_val_766_, lean_object* v_info_767_, lean_object* v___x_768_, lean_object* v_val_769_, lean_object* v___x_770_, lean_object* v_as_x27_771_, lean_object* v_b_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
uint8_t v___x_22560__boxed_775_; lean_object* v_res_776_; 
v___x_22560__boxed_775_ = lean_unbox(v___x_770_);
v_res_776_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_765_, v_val_766_, v_info_767_, v___x_768_, v_val_769_, v___x_22560__boxed_775_, v_as_x27_771_, v_b_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec(v_as_x27_771_);
lean_dec_ref(v_info_767_);
lean_dec(v_val_766_);
lean_dec_ref(v_str_765_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_777_, v___y_779_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v___x_783_);
v___x_785_ = lean_whnf(v_a_784_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
return v___x_785_;
}
else
{
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_793_, lean_object* v___x_794_, lean_object* v_val_795_, lean_object* v___x_796_, lean_object* v_ci_797_, lean_object* v_info_798_, lean_object* v_x_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
if (lean_obj_tag(v_info_798_) == 1)
{
lean_object* v_i_803_; lean_object* v_expr_804_; 
v_i_803_ = lean_ctor_get(v_info_798_, 0);
v_expr_804_ = lean_ctor_get(v_i_803_, 3);
if (lean_obj_tag(v_expr_804_) == 1)
{
lean_object* v_lctx_805_; lean_object* v_expectedType_x3f_806_; uint8_t v_isBinder_807_; lean_object* v_fvarId_808_; lean_object* v___x_809_; 
v_lctx_805_ = lean_ctor_get(v_i_803_, 1);
v_expectedType_x3f_806_ = lean_ctor_get(v_i_803_, 2);
v_isBinder_807_ = lean_ctor_get_uint8(v_i_803_, sizeof(void*)*4);
v_fvarId_808_ = lean_ctor_get(v_expr_804_, 0);
v___x_809_ = l_Lean_Elab_Info_range_x3f(v_info_798_);
if (lean_obj_tag(v___x_809_) == 1)
{
lean_object* v_val_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_965_; 
v_val_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_965_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_965_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_val_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_965_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_st_ref_get(v_val_793_);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_814_, v_val_810_);
lean_dec(v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = l_Lean_Elab_Info_stx(v_info_798_);
v___x_817_ = l_Lean_Syntax_getHeadInfo(v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref(v___x_817_);
if (v_isBinder_807_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v___x_816_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 0);
lean_ctor_set(v___x_812_, 0, v___x_794_);
v___x_819_ = v___x_812_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_794_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
else
{
lean_object* v___x_821_; 
lean_inc(v_fvarId_808_);
lean_inc_ref(v_lctx_805_);
v___x_821_ = lean_local_ctx_find(v_lctx_805_, v_fvarId_808_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_val_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_955_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_955_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_955_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_val_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_955_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_start_826_; uint8_t v___x_827_; 
v_start_826_ = lean_ctor_get(v_val_810_, 0);
v___x_827_ = l_Lean_Syntax_Range_contains(v_val_795_, v_start_826_, v___x_815_);
if (v___x_827_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v_val_822_);
lean_dec(v___x_816_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_794_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_794_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
if (v___x_815_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = l_Lean_LocalDecl_userName(v_val_822_);
lean_dec(v_val_822_);
v___x_832_ = l_Lean_Name_hasMacroScopes(v___x_831_);
lean_dec(v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v_toCommandContextInfo_833_; lean_object* v_options_834_; lean_object* v___x_835_; 
v_toCommandContextInfo_833_ = lean_ctor_get(v_ci_797_, 0);
v_options_834_ = lean_ctor_get(v_toCommandContextInfo_833_, 4);
lean_inc_ref(v_options_834_);
v___x_835_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_834_, v___y_801_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_940_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_940_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_940_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_940_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Linter_getLinterValue(v___x_796_, v_a_836_);
lean_dec(v_a_836_);
if (v___x_840_ == 0)
{
lean_object* v___x_842_; 
lean_del_object(v___x_824_);
lean_dec(v___x_816_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_794_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_794_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Syntax_getId(v___x_816_);
lean_dec(v___x_816_);
if (lean_obj_tag(v___x_844_) == 1)
{
lean_object* v_pre_845_; lean_object* v_str_846_; lean_object* v_ty_848_; lean_object* v___y_849_; lean_object* v___y_850_; 
v_pre_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_pre_845_);
v_str_846_ = lean_ctor_get(v___x_844_, 1);
lean_inc_ref(v_str_846_);
if (lean_obj_tag(v_pre_845_) == 0)
{
lean_del_object(v___x_838_);
if (lean_obj_tag(v_expectedType_x3f_806_) == 1)
{
lean_object* v_val_907_; 
lean_del_object(v___x_812_);
v_val_907_ = lean_ctor_get(v_expectedType_x3f_806_, 0);
lean_inc(v_val_907_);
v_ty_848_ = v_val_907_;
v___y_849_ = v___y_800_;
v___y_850_ = v___y_801_;
goto v___jp_847_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_inc_ref(v_expr_804_);
v___x_908_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_908_, 0, v_expr_804_);
lean_inc_ref(v_ci_797_);
lean_inc_ref(v_i_803_);
v___x_909_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_803_, v_ci_797_, v___x_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; 
lean_del_object(v___x_812_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref(v___x_909_);
v_ty_848_ = v_a_910_;
v___y_849_ = v___y_800_;
v___y_850_ = v___y_801_;
goto v___jp_847_;
}
else
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_str_846_);
lean_dec_ref(v___x_844_);
lean_del_object(v___x_824_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
v_isSharedCheck_931_ = !lean_is_exclusive(v_val_810_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; lean_object* v_unused_933_; 
v_unused_932_ = lean_ctor_get(v_val_810_, 1);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_val_810_, 0);
lean_dec(v_unused_933_);
v___x_912_ = v_val_810_;
v_isShared_913_ = v_isSharedCheck_931_;
goto v_resetjp_911_;
}
else
{
lean_dec(v_val_810_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_931_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_930_; 
v_a_914_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_930_ == 0)
{
v___x_916_ = v___x_909_;
v_isShared_917_ = v_isSharedCheck_930_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_909_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_930_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_ref_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v_ref_918_ = lean_ctor_get(v___y_800_, 7);
v___x_919_ = lean_io_error_to_string(v_a_914_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 3);
lean_ctor_set(v___x_812_, 0, v___x_919_);
v___x_921_ = v___x_812_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_929_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = l_Lean_MessageData_ofFormat(v___x_921_);
lean_inc(v_ref_918_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_922_);
lean_ctor_set(v___x_912_, 0, v_ref_918_);
v___x_924_ = v___x_912_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_ref_918_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_924_);
v___x_926_ = v___x_916_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
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
lean_object* v___x_935_; 
lean_dec_ref(v_str_846_);
lean_dec(v_pre_845_);
lean_dec_ref(v___x_844_);
lean_del_object(v___x_824_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_794_);
v___x_935_ = v___x_838_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_794_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
v___jp_847_:
{
lean_object* v___f_851_; lean_object* v___x_852_; 
v___f_851_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_851_, 0, v_ty_848_);
lean_inc_ref(v_i_803_);
v___x_852_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_803_, v_ci_797_, v___f_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_824_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_883_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_883_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_883_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Expr_getAppFn_x27(v_a_853_);
lean_dec(v_a_853_);
if (lean_obj_tag(v___x_857_) == 4)
{
lean_object* v_declName_858_; lean_object* v___x_859_; lean_object* v_env_860_; lean_object* v___x_861_; 
v_declName_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_declName_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = lean_st_ref_get(v___y_850_);
v_env_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc_ref(v_env_860_);
lean_dec(v___x_859_);
v___x_861_ = l_Lean_Environment_find_x3f(v_env_860_, v_declName_858_, v___x_815_);
if (lean_obj_tag(v___x_861_) == 1)
{
lean_object* v_val_862_; 
v_val_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_val_862_);
lean_dec_ref(v___x_861_);
if (lean_obj_tag(v_val_862_) == 5)
{
lean_object* v_val_863_; lean_object* v_ctors_864_; lean_object* v___x_865_; 
lean_del_object(v___x_855_);
v_val_863_ = lean_ctor_get(v_val_862_, 0);
lean_inc_ref(v_val_863_);
lean_dec_ref(v_val_862_);
v_ctors_864_ = lean_ctor_get(v_val_863_, 4);
lean_inc(v_ctors_864_);
lean_dec_ref(v_val_863_);
v___x_865_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_846_, v_val_793_, v_info_798_, v___x_844_, v_val_810_, v___x_815_, v_ctors_864_, v___x_794_, v___y_850_);
lean_dec(v_ctors_864_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_str_846_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___x_865_, 0);
lean_dec(v_unused_873_);
v___x_867_ = v___x_865_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_dec(v___x_865_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_794_);
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_794_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
return v___x_865_;
}
}
else
{
lean_object* v___x_875_; 
lean_dec(v_val_862_);
lean_dec_ref(v_str_846_);
lean_dec_ref(v___x_844_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_794_);
v___x_875_ = v___x_855_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_794_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v___x_861_);
lean_dec_ref(v_str_846_);
lean_dec_ref(v___x_844_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_794_);
v___x_878_ = v___x_855_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_794_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v___x_881_; 
lean_dec_ref(v___x_857_);
lean_dec_ref(v_str_846_);
lean_dec_ref(v___x_844_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_794_);
v___x_881_ = v___x_855_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_794_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_str_846_);
lean_dec_ref(v___x_844_);
lean_dec_ref(v_info_798_);
v_isSharedCheck_904_ = !lean_is_exclusive(v_val_810_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; lean_object* v_unused_906_; 
v_unused_905_ = lean_ctor_get(v_val_810_, 1);
lean_dec(v_unused_905_);
v_unused_906_ = lean_ctor_get(v_val_810_, 0);
lean_dec(v_unused_906_);
v___x_885_ = v_val_810_;
v_isShared_886_ = v_isSharedCheck_904_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_val_810_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_904_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_903_; 
v_a_887_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_903_ == 0)
{
v___x_889_ = v___x_852_;
v_isShared_890_ = v_isSharedCheck_903_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_852_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_903_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_ref_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v_ref_891_ = lean_ctor_get(v___y_849_, 7);
v___x_892_ = lean_io_error_to_string(v_a_887_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 3);
lean_ctor_set(v___x_824_, 0, v___x_892_);
v___x_894_ = v___x_824_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_902_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_897_; 
v___x_895_ = l_Lean_MessageData_ofFormat(v___x_894_);
lean_inc(v_ref_891_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_895_);
lean_ctor_set(v___x_885_, 0, v_ref_891_);
v___x_897_ = v___x_885_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_ref_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_895_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_897_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
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
lean_object* v___x_938_; 
lean_dec(v___x_844_);
lean_del_object(v___x_824_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_794_);
v___x_938_ = v___x_838_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_794_);
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
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_del_object(v___x_824_);
lean_dec(v___x_816_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
v_a_941_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_835_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_835_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v___x_950_; 
lean_dec(v___x_816_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_794_);
v___x_950_ = v___x_824_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_794_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
else
{
lean_object* v___x_953_; 
lean_dec(v_val_822_);
lean_dec(v___x_816_);
lean_del_object(v___x_812_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_794_);
v___x_953_ = v___x_824_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_794_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
else
{
lean_object* v___x_957_; 
lean_dec(v___x_821_);
lean_dec(v___x_816_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 0);
lean_ctor_set(v___x_812_, 0, v___x_794_);
v___x_957_ = v___x_812_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_794_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v___x_817_);
lean_dec(v___x_816_);
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 0);
lean_ctor_set(v___x_812_, 0, v___x_794_);
v___x_960_ = v___x_812_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_794_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
else
{
lean_object* v___x_963_; 
lean_dec(v_val_810_);
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 0);
lean_ctor_set(v___x_812_, 0, v___x_794_);
v___x_963_ = v___x_812_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_794_);
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
else
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec(v___x_809_);
lean_dec_ref(v_ci_797_);
v_isSharedCheck_972_ = !lean_is_exclusive(v_info_798_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v_info_798_, 0);
lean_dec(v_unused_973_);
v___x_967_ = v_info_798_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_dec(v_info_798_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 0);
lean_ctor_set(v___x_967_, 0, v___x_794_);
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_794_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_ci_797_);
v_isSharedCheck_980_ = !lean_is_exclusive(v_info_798_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v_info_798_, 0);
lean_dec(v_unused_981_);
v___x_975_ = v_info_798_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_dec(v_info_798_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
lean_ctor_set(v___x_975_, 0, v___x_794_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_794_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v___x_982_; 
lean_dec_ref(v_info_798_);
lean_dec_ref(v_ci_797_);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_794_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_983_, lean_object* v___x_984_, lean_object* v_val_985_, lean_object* v___x_986_, lean_object* v_ci_987_, lean_object* v_info_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_983_, v___x_984_, v_val_985_, v___x_986_, v_ci_987_, v_info_988_, v_x_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v_x_989_);
lean_dec_ref(v___x_986_);
lean_dec_ref(v_val_985_);
lean_dec(v_val_983_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_994_, lean_object* v_ci_995_, lean_object* v_i_996_, lean_object* v_cs_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
lean_inc(v___y_1000_);
lean_inc_ref(v___y_999_);
v___x_1002_ = lean_apply_6(v_postNode_994_, v_ci_995_, v_i_996_, v_cs_997_, v___y_999_, v___y_1000_, lean_box(0));
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1003_, lean_object* v_ci_1004_, lean_object* v_i_1005_, lean_object* v_cs_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1003_, v_ci_1004_, v_i_1005_, v_cs_1006_, v_x_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v_x_1007_);
return v_res_1011_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_instMonadEIO(lean_box(0));
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v_toApplicative_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1052_; 
v___x_1019_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1020_ = l_StateRefT_x27_instMonad___redArg(v___x_1019_);
v_toApplicative_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_1020_, 1);
lean_dec(v_unused_1053_);
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1052_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_toApplicative_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1052_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v_toFunctor_1025_; lean_object* v_toSeq_1026_; lean_object* v_toSeqLeft_1027_; lean_object* v_toSeqRight_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1050_; 
v_toFunctor_1025_ = lean_ctor_get(v_toApplicative_1021_, 0);
v_toSeq_1026_ = lean_ctor_get(v_toApplicative_1021_, 2);
v_toSeqLeft_1027_ = lean_ctor_get(v_toApplicative_1021_, 3);
v_toSeqRight_1028_ = lean_ctor_get(v_toApplicative_1021_, 4);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_toApplicative_1021_);
if (v_isSharedCheck_1050_ == 0)
{
lean_object* v_unused_1051_; 
v_unused_1051_ = lean_ctor_get(v_toApplicative_1021_, 1);
lean_dec(v_unused_1051_);
v___x_1030_ = v_toApplicative_1021_;
v_isShared_1031_ = v_isSharedCheck_1050_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_toSeqRight_1028_);
lean_inc(v_toSeqLeft_1027_);
lean_inc(v_toSeq_1026_);
lean_inc(v_toFunctor_1025_);
lean_dec(v_toApplicative_1021_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1050_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___f_1039_; lean_object* v___x_1041_; 
v___f_1032_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1033_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1025_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toFunctor_1025_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toFunctor_1025_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___f_1034_);
lean_ctor_set(v___x_1036_, 1, v___f_1035_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toSeqRight_1028_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toSeqLeft_1027_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeq_1026_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 4, v___f_1037_);
lean_ctor_set(v___x_1030_, 3, v___f_1038_);
lean_ctor_set(v___x_1030_, 2, v___f_1039_);
lean_ctor_set(v___x_1030_, 1, v___f_1032_);
lean_ctor_set(v___x_1030_, 0, v___x_1036_);
v___x_1041_ = v___x_1030_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___f_1032_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v___f_1039_);
lean_ctor_set(v_reuseFailAlloc_1049_, 3, v___f_1038_);
lean_ctor_set(v_reuseFailAlloc_1049_, 4, v___f_1037_);
v___x_1041_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1043_; 
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___f_1033_);
lean_ctor_set(v___x_1023_, 0, v___x_1041_);
v___x_1043_ = v___x_1023_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___f_1033_);
v___x_1043_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_18807__overap_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_instInhabitedOfMonad___redArg(v___x_1043_, v___x_1044_);
v___x_18807__overap_1046_ = lean_panic_fn_borrowed(v___x_1045_, v_msg_1015_);
lean_dec(v___x_1045_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1047_ = lean_apply_3(v___x_18807__overap_1046_, v___y_1016_, v___y_1017_, lean_box(0));
return v___x_1047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1058_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1063_ = lean_unsigned_to_nat(21u);
v___x_1064_ = lean_unsigned_to_nat(65u);
v___x_1065_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1066_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1067_ = l_mkPanicMessageWithDecl(v___x_1066_, v___x_1065_, v___x_1064_, v___x_1063_, v___x_1062_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1068_, lean_object* v_postNode_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
switch(lean_obj_tag(v_x_1071_))
{
case 0:
{
lean_object* v_i_1075_; lean_object* v_t_1076_; lean_object* v___x_1077_; 
v_i_1075_ = lean_ctor_get(v_x_1071_, 0);
lean_inc_ref(v_i_1075_);
v_t_1076_ = lean_ctor_get(v_x_1071_, 1);
lean_inc_ref(v_t_1076_);
lean_dec_ref(v_x_1071_);
v___x_1077_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1075_, v_x_1070_);
v_x_1070_ = v___x_1077_;
v_x_1071_ = v_t_1076_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1070_) == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec_ref(v_x_1071_);
lean_dec_ref(v_postNode_1069_);
lean_dec_ref(v_preNode_1068_);
v___x_1079_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1080_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1079_, v___y_1072_, v___y_1073_);
return v___x_1080_;
}
else
{
lean_object* v_i_1081_; lean_object* v_children_1082_; lean_object* v_val_1083_; lean_object* v___x_1084_; 
v_i_1081_ = lean_ctor_get(v_x_1071_, 0);
lean_inc_ref_n(v_i_1081_, 2);
v_children_1082_ = lean_ctor_get(v_x_1071_, 1);
lean_inc_ref_n(v_children_1082_, 2);
lean_dec_ref(v_x_1071_);
v_val_1083_ = lean_ctor_get(v_x_1070_, 0);
lean_inc_n(v_val_1083_, 2);
lean_inc_ref(v_preNode_1068_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
v___x_1084_ = lean_apply_6(v_preNode_1068_, v_val_1083_, v_i_1081_, v_children_1082_, v___y_1072_, v___y_1073_, lean_box(0));
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; uint8_t v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v___x_1086_ = lean_unbox(v_a_1085_);
lean_dec(v_a_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v_preNode_1068_);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_x_1070_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v_x_1070_, 0);
lean_dec(v_unused_1112_);
v___x_1088_ = v_x_1070_;
v_isShared_1089_ = v_isSharedCheck_1111_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v_x_1070_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1111_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_box(0);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
v___x_1091_ = lean_apply_7(v_postNode_1069_, v_val_1083_, v_i_1081_, v_children_1082_, v___x_1090_, v___y_1072_, v___y_1073_, lean_box(0));
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v_a_1092_);
v___x_1097_ = v___x_1088_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
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
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_del_object(v___x_1088_);
v_a_1103_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1091_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1091_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
else
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1113_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1070_, v_i_1081_);
v___x_1114_ = l_Lean_PersistentArray_toList___redArg(v_children_1082_);
v___x_1115_ = lean_box(0);
lean_inc_ref(v_postNode_1069_);
v___x_1116_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1068_, v_postNode_1069_, v___x_1113_, v___x_1114_, v___x_1115_, v___y_1072_, v___y_1073_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
lean_inc(v___y_1073_);
lean_inc_ref(v___y_1072_);
v___x_1118_ = lean_apply_7(v_postNode_1069_, v_val_1083_, v_i_1081_, v_children_1082_, v_a_1117_, v___y_1072_, v___y_1073_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1123_, 0, v_a_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
v_a_1128_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1118_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1118_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
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
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec(v_val_1083_);
lean_dec_ref(v_children_1082_);
lean_dec_ref(v_i_1081_);
lean_dec_ref(v_postNode_1069_);
v_a_1136_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1116_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1116_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_val_1083_);
lean_dec_ref(v_children_1082_);
lean_dec_ref(v_x_1070_);
lean_dec_ref(v_i_1081_);
lean_dec_ref(v_postNode_1069_);
lean_dec_ref(v_preNode_1068_);
v_a_1144_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1084_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1084_);
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
default: 
{
lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_x_1070_);
lean_dec_ref(v_postNode_1069_);
lean_dec_ref(v_preNode_1068_);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1159_ == 0)
{
lean_object* v_unused_1160_; 
v_unused_1160_ = lean_ctor_get(v_x_1071_, 0);
lean_dec(v_unused_1160_);
v___x_1153_ = v_x_1071_;
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
else
{
lean_dec(v_x_1071_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1159_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1155_ = lean_box(0);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1155_);
v___x_1157_ = v___x_1153_;
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1161_, lean_object* v_postNode_1162_, lean_object* v___x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v___x_1163_);
lean_dec_ref(v_postNode_1162_);
lean_dec_ref(v_preNode_1161_);
v___x_1169_ = l_List_reverse___redArg(v_x_1165_);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v_head_1171_; lean_object* v_tail_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1190_; 
v_head_1171_ = lean_ctor_get(v_x_1164_, 0);
v_tail_1172_ = lean_ctor_get(v_x_1164_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1174_ = v_x_1164_;
v_isShared_1175_ = v_isSharedCheck_1190_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_tail_1172_);
lean_inc(v_head_1171_);
lean_dec(v_x_1164_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1190_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; 
lean_inc(v___x_1163_);
lean_inc_ref(v_postNode_1162_);
lean_inc_ref(v_preNode_1161_);
v___x_1176_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1161_, v_postNode_1162_, v___x_1163_, v_head_1171_, v___y_1166_, v___y_1167_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref(v___x_1176_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 1, v_x_1165_);
lean_ctor_set(v___x_1174_, 0, v_a_1177_);
v___x_1179_ = v___x_1174_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1177_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_x_1165_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
v_x_1164_ = v_tail_1172_;
v_x_1165_ = v___x_1179_;
goto _start;
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_del_object(v___x_1174_);
lean_dec(v_tail_1172_);
lean_dec(v_x_1165_);
lean_dec(v___x_1163_);
lean_dec_ref(v_postNode_1162_);
lean_dec_ref(v_preNode_1161_);
v_a_1182_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1176_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1176_);
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
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1191_, lean_object* v_postNode_1192_, lean_object* v___x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1191_, v_postNode_1192_, v___x_1193_, v_x_1194_, v_x_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1200_, lean_object* v_postNode_1201_, lean_object* v_x_1202_, lean_object* v_x_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1200_, v_postNode_1201_, v_x_1202_, v_x_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1208_, lean_object* v_postNode_1209_, lean_object* v_ctx_x3f_1210_, lean_object* v_t_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___f_1215_; lean_object* v___x_1216_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1215_, 0, v_postNode_1209_);
v___x_1216_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1208_, v___f_1215_, v_ctx_x3f_1210_, v_t_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1225_);
v___x_1218_ = v___x_1216_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v___x_1216_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1216_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1216_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1234_, lean_object* v_postNode_1235_, lean_object* v_ctx_x3f_1236_, lean_object* v_t_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1234_, v_postNode_1235_, v_ctx_x3f_1236_, v_t_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1242_, lean_object* v_val_1243_, lean_object* v_val_1244_, lean_object* v_as_1245_, size_t v_sz_1246_, size_t v_i_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1247_, v_sz_1246_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v_val_1244_);
lean_dec(v_val_1243_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_b_1248_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___f_1258_; lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1254_ = lean_box(v___x_1242_);
v___f_1255_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1255_, 0, v___x_1254_);
v___x_1256_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1257_ = lean_box(0);
lean_inc_ref(v_val_1244_);
lean_inc(v_val_1243_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1258_, 0, v_val_1243_);
lean_closure_set(v___f_1258_, 1, v___x_1257_);
lean_closure_set(v___f_1258_, 2, v_val_1244_);
lean_closure_set(v___f_1258_, 3, v___x_1256_);
v_a_1259_ = lean_array_uget_borrowed(v_as_1245_, v_i_1247_);
v___x_1260_ = lean_box(0);
lean_inc(v_a_1259_);
v___x_1261_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1255_, v___f_1258_, v___x_1260_, v_a_1259_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1261_) == 0)
{
size_t v___x_1262_; size_t v___x_1263_; 
lean_dec_ref(v___x_1261_);
v___x_1262_ = ((size_t)1ULL);
v___x_1263_ = lean_usize_add(v_i_1247_, v___x_1262_);
v_i_1247_ = v___x_1263_;
v_b_1248_ = v___x_1257_;
goto _start;
}
else
{
lean_dec_ref(v_val_1244_);
lean_dec(v_val_1243_);
return v___x_1261_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1265_, lean_object* v_val_1266_, lean_object* v_val_1267_, lean_object* v_as_1268_, lean_object* v_sz_1269_, lean_object* v_i_1270_, lean_object* v_b_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v___x_23424__boxed_1275_; size_t v_sz_boxed_1276_; size_t v_i_boxed_1277_; lean_object* v_res_1278_; 
v___x_23424__boxed_1275_ = lean_unbox(v___x_1265_);
v_sz_boxed_1276_ = lean_unbox_usize(v_sz_1269_);
lean_dec(v_sz_1269_);
v_i_boxed_1277_ = lean_unbox_usize(v_i_1270_);
lean_dec(v_i_1270_);
v_res_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23424__boxed_1275_, v_val_1266_, v_val_1267_, v_as_1268_, v_sz_boxed_1276_, v_i_boxed_1277_, v_b_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec_ref(v_as_1268_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 0)
{
return v_x_1279_;
}
else
{
lean_object* v_key_1281_; lean_object* v_value_1282_; lean_object* v_tail_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v_key_1281_ = lean_ctor_get(v_x_1280_, 0);
v_value_1282_ = lean_ctor_get(v_x_1280_, 1);
v_tail_1283_ = lean_ctor_get(v_x_1280_, 2);
lean_inc(v_value_1282_);
lean_inc(v_key_1281_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_key_1281_);
lean_ctor_set(v___x_1284_, 1, v_value_1282_);
v___x_1285_ = lean_array_push(v_x_1279_, v___x_1284_);
v_x_1279_ = v___x_1285_;
v_x_1280_ = v_tail_1283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1287_, v_x_1288_);
lean_dec(v_x_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1290_, size_t v_i_1291_, size_t v_stop_1292_, lean_object* v_b_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_usize_dec_eq(v_i_1291_, v_stop_1292_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; size_t v___x_1297_; size_t v___x_1298_; 
v___x_1295_ = lean_array_uget_borrowed(v_as_1290_, v_i_1291_);
v___x_1296_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1293_, v___x_1295_);
v___x_1297_ = ((size_t)1ULL);
v___x_1298_ = lean_usize_add(v_i_1291_, v___x_1297_);
v_i_1291_ = v___x_1298_;
v_b_1293_ = v___x_1296_;
goto _start;
}
else
{
return v_b_1293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1300_, lean_object* v_i_1301_, lean_object* v_stop_1302_, lean_object* v_b_1303_){
_start:
{
size_t v_i_boxed_1304_; size_t v_stop_boxed_1305_; lean_object* v_res_1306_; 
v_i_boxed_1304_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_stop_boxed_1305_ = lean_unbox_usize(v_stop_1302_);
lean_dec(v_stop_1302_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1300_, v_i_boxed_1304_, v_stop_boxed_1305_, v_b_1303_);
lean_dec_ref(v_as_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v___x_1310_; lean_object* v_scopes_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_opts_1314_; lean_object* v___x_1315_; 
v___x_1310_ = lean_st_ref_get(v___y_1308_);
v_scopes_1311_ = lean_ctor_get(v___x_1310_, 2);
lean_inc(v_scopes_1311_);
lean_dec(v___x_1310_);
v___x_1312_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1313_ = l_List_head_x21___redArg(v___x_1312_, v_scopes_1311_);
lean_dec(v_scopes_1311_);
v_opts_1314_ = lean_ctor_get(v___x_1313_, 1);
lean_inc_ref(v_opts_1314_);
lean_dec(v___x_1313_);
v___x_1315_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1314_, v___y_1308_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1319_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_unsigned_to_nat(16u);
v___x_1322_ = lean_mk_array(v___x_1321_, v___x_1320_);
return v___x_1322_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1323_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1401_; 
v___x_1330_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1327_, v___y_1328_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1401_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1401_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1336_ = l_Lean_Linter_getLinterValue(v___x_1335_, v_a_1331_);
lean_dec(v_a_1331_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
uint8_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = 0;
v___x_1342_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1326_, v___x_1341_);
if (lean_obj_tag(v___x_1342_) == 1)
{
lean_object* v_val_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_infoState_1348_; lean_object* v_trees_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; size_t v_sz_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
lean_del_object(v___x_1333_);
v_val_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_val_1343_);
lean_dec_ref(v___x_1342_);
v___x_1344_ = lean_st_ref_get(v___y_1328_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1347_ = lean_st_mk_ref(v___x_1346_);
v_infoState_1348_ = lean_ctor_get(v___x_1344_, 8);
lean_inc_ref(v_infoState_1348_);
lean_dec(v___x_1344_);
v_trees_1349_ = lean_ctor_get(v_infoState_1348_, 2);
lean_inc_ref(v_trees_1349_);
lean_dec_ref(v_infoState_1348_);
v___x_1350_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1349_);
lean_dec_ref(v_trees_1349_);
v___x_1351_ = lean_box(0);
v_sz_1352_ = lean_array_size(v___x_1350_);
v___x_1353_ = ((size_t)0ULL);
lean_inc(v___x_1347_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1336_, v___x_1347_, v_val_1343_, v___x_1350_, v_sz_1352_, v___x_1353_, v___x_1351_, v___y_1327_, v___y_1328_);
lean_dec_ref(v___x_1350_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; lean_object* v___y_1357_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1381_; lean_object* v_size_1387_; lean_object* v_buckets_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
lean_dec_ref(v___x_1354_);
v___x_1355_ = lean_st_ref_get(v___x_1347_);
lean_dec(v___x_1347_);
v_size_1387_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_size_1387_);
v_buckets_1388_ = lean_ctor_get(v___x_1355_, 1);
lean_inc_ref(v_buckets_1388_);
lean_dec(v___x_1355_);
v___x_1389_ = lean_mk_empty_array_with_capacity(v_size_1387_);
lean_dec(v_size_1387_);
v___x_1390_ = lean_array_get_size(v_buckets_1388_);
v___x_1391_ = lean_nat_dec_lt(v___x_1345_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_dec_ref(v_buckets_1388_);
v___y_1381_ = v___x_1389_;
goto v___jp_1380_;
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_le(v___x_1390_, v___x_1390_);
if (v___x_1392_ == 0)
{
if (v___x_1391_ == 0)
{
lean_dec_ref(v_buckets_1388_);
v___y_1381_ = v___x_1389_;
goto v___jp_1380_;
}
else
{
size_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = lean_usize_of_nat(v___x_1390_);
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1388_, v___x_1353_, v___x_1393_, v___x_1389_);
lean_dec_ref(v_buckets_1388_);
v___y_1381_ = v___x_1394_;
goto v___jp_1380_;
}
}
else
{
size_t v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_usize_of_nat(v___x_1390_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1388_, v___x_1353_, v___x_1395_, v___x_1389_);
lean_dec_ref(v_buckets_1388_);
v___y_1381_ = v___x_1396_;
goto v___jp_1380_;
}
}
v___jp_1356_:
{
size_t v_sz_1358_; lean_object* v___x_1359_; 
v_sz_1358_ = lean_array_size(v___y_1357_);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1357_, v_sz_1358_, v___x_1353_, v___x_1351_, v___y_1327_, v___y_1328_);
lean_dec_ref(v___y_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1359_, 0);
lean_dec(v_unused_1367_);
v___x_1361_ = v___x_1359_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v___x_1359_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1351_);
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1351_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
else
{
return v___x_1359_;
}
}
v___jp_1368_:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1369_, v___y_1371_, v___y_1370_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec(v___y_1369_);
v___y_1357_ = v___x_1373_;
goto v___jp_1356_;
}
v___jp_1374_:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_nat_dec_le(v___y_1378_, v___y_1376_);
if (v___x_1379_ == 0)
{
lean_dec(v___y_1376_);
lean_inc(v___y_1378_);
v___y_1369_ = v___y_1375_;
v___y_1370_ = v___y_1378_;
v___y_1371_ = v___y_1377_;
v___y_1372_ = v___y_1378_;
goto v___jp_1368_;
}
else
{
v___y_1369_ = v___y_1375_;
v___y_1370_ = v___y_1378_;
v___y_1371_ = v___y_1377_;
v___y_1372_ = v___y_1376_;
goto v___jp_1368_;
}
}
v___jp_1380_:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = lean_array_get_size(v___y_1381_);
v___x_1383_ = lean_nat_dec_eq(v___x_1382_, v___x_1345_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = lean_unsigned_to_nat(1u);
v___x_1385_ = lean_nat_sub(v___x_1382_, v___x_1384_);
v___x_1386_ = lean_nat_dec_le(v___x_1345_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_inc(v___x_1385_);
v___y_1375_ = v___x_1382_;
v___y_1376_ = v___x_1385_;
v___y_1377_ = v___y_1381_;
v___y_1378_ = v___x_1385_;
goto v___jp_1374_;
}
else
{
v___y_1375_ = v___x_1382_;
v___y_1376_ = v___x_1385_;
v___y_1377_ = v___y_1381_;
v___y_1378_ = v___x_1345_;
goto v___jp_1374_;
}
}
else
{
v___y_1357_ = v___y_1381_;
goto v___jp_1356_;
}
}
}
else
{
lean_dec(v___x_1347_);
return v___x_1354_;
}
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_dec(v___x_1342_);
v___x_1397_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1397_);
v___x_1399_ = v___x_1333_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v_cmdStx_1402_);
return v_res_1406_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1416_, lean_object* v_m_1417_, lean_object* v_a_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1417_, v_a_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1420_, lean_object* v_m_1421_, lean_object* v_a_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1420_, v_m_1421_, v_a_1422_);
lean_dec_ref(v_a_1422_);
lean_dec_ref(v_m_1421_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1425_, lean_object* v_m_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1426_, v_a_1427_, v_b_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1430_, lean_object* v_val_1431_, lean_object* v_info_1432_, lean_object* v___x_1433_, lean_object* v_val_1434_, uint8_t v___x_1435_, lean_object* v_as_1436_, lean_object* v_as_x27_1437_, lean_object* v_b_1438_, lean_object* v_a_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1430_, v_val_1431_, v_info_1432_, v___x_1433_, v_val_1434_, v___x_1435_, v_as_x27_1437_, v_b_1438_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1444_, lean_object* v_val_1445_, lean_object* v_info_1446_, lean_object* v___x_1447_, lean_object* v_val_1448_, lean_object* v___x_1449_, lean_object* v_as_1450_, lean_object* v_as_x27_1451_, lean_object* v_b_1452_, lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v___x_23716__boxed_1457_; lean_object* v_res_1458_; 
v___x_23716__boxed_1457_ = lean_unbox(v___x_1449_);
v_res_1458_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1444_, v_val_1445_, v_info_1446_, v___x_1447_, v_val_1448_, v___x_23716__boxed_1457_, v_as_1450_, v_as_x27_1451_, v_b_1452_, v_a_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v_as_x27_1451_);
lean_dec(v_as_1450_);
lean_dec_ref(v_info_1446_);
lean_dec(v_val_1445_);
lean_dec_ref(v_str_1444_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1459_, lean_object* v_as_1460_, lean_object* v_lo_1461_, lean_object* v_hi_1462_, lean_object* v_w_1463_, lean_object* v_hlo_1464_, lean_object* v_hhi_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1459_, v_as_1460_, v_lo_1461_, v_hi_1462_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1467_, lean_object* v_as_1468_, lean_object* v_lo_1469_, lean_object* v_hi_1470_, lean_object* v_w_1471_, lean_object* v_hlo_1472_, lean_object* v_hhi_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1467_, v_as_1468_, v_lo_1469_, v_hi_1470_, v_w_1471_, v_hlo_1472_, v_hhi_1473_);
lean_dec(v_hi_1470_);
lean_dec(v_n_1467_);
return v_res_1474_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1475_, lean_object* v_a_1476_, lean_object* v_x_1477_){
_start:
{
uint8_t v___x_1478_; 
v___x_1478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1476_, v_x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1479_, lean_object* v_a_1480_, lean_object* v_x_1481_){
_start:
{
uint8_t v_res_1482_; lean_object* v_r_1483_; 
v_res_1482_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1479_, v_a_1480_, v_x_1481_);
lean_dec(v_x_1481_);
lean_dec_ref(v_a_1480_);
v_r_1483_ = lean_box(v_res_1482_);
return v_r_1483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1484_, lean_object* v_data_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_b_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1488_, v_b_1489_, v_x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1492_, lean_object* v_msg_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1493_, v___y_1494_, v___y_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1498_, lean_object* v_msg_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1498_, v_msg_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1504_, lean_object* v_preNode_1505_, lean_object* v_postNode_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1505_, v_postNode_1506_, v_x_1507_, v_x_1508_, v___y_1509_, v___y_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1513_, lean_object* v_preNode_1514_, lean_object* v_postNode_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1513_, v_preNode_1514_, v_postNode_1515_, v_x_1516_, v_x_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object* v_n_1522_, lean_object* v_lo_1523_, lean_object* v_hi_1524_, lean_object* v_hhi_1525_, lean_object* v_pivot_1526_, lean_object* v_as_1527_, lean_object* v_i_1528_, lean_object* v_k_1529_, lean_object* v_ilo_1530_, lean_object* v_ik_1531_, lean_object* v_w_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1524_, v_pivot_1526_, v_as_1527_, v_i_1528_, v_k_1529_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object* v_n_1534_, lean_object* v_lo_1535_, lean_object* v_hi_1536_, lean_object* v_hhi_1537_, lean_object* v_pivot_1538_, lean_object* v_as_1539_, lean_object* v_i_1540_, lean_object* v_k_1541_, lean_object* v_ilo_1542_, lean_object* v_ik_1543_, lean_object* v_w_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_1534_, v_lo_1535_, v_hi_1536_, v_hhi_1537_, v_pivot_1538_, v_as_1539_, v_i_1540_, v_k_1541_, v_ilo_1542_, v_ik_1543_, v_w_1544_);
lean_dec_ref(v_pivot_1538_);
lean_dec(v_hi_1536_);
lean_dec(v_lo_1535_);
lean_dec(v_n_1534_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1546_, lean_object* v_i_1547_, lean_object* v_source_1548_, lean_object* v_target_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1547_, v_source_1548_, v_target_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1551_, lean_object* v_preNode_1552_, lean_object* v_postNode_1553_, lean_object* v___x_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1552_, v_postNode_1553_, v___x_1554_, v_x_1555_, v_x_1556_, v___y_1557_, v___y_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1561_, lean_object* v_preNode_1562_, lean_object* v_postNode_1563_, lean_object* v___x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1561_, v_preNode_1562_, v_postNode_1563_, v___x_1564_, v_x_1565_, v_x_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1571_, v___y_1573_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1582_, v_x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1587_ = l_Lean_Elab_Command_addLinter(v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1589_;
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
