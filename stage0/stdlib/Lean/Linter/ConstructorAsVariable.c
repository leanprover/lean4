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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Linter_linterMessageTag;
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
lean_object* v___x_62_; lean_object* v_env_63_; lean_object* v___x_64_; lean_object* v_toEnvExtension_65_; lean_object* v_asyncMode_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_merged_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v___x_62_ = lean_st_ref_get(v___y_60_);
v_env_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc_ref(v_env_63_);
lean_dec(v___x_62_);
v___x_64_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_65_ = lean_ctor_get(v___x_64_, 0);
v_asyncMode_66_ = lean_ctor_get(v_toEnvExtension_65_, 2);
v___x_67_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_68_ = lean_box(0);
v___x_69_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_67_, v___x_64_, v_env_63_, v_asyncMode_66_, v___x_68_);
v_merged_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v___x_69_, 1);
lean_dec(v_unused_79_);
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_merged_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_75_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v_merged_70_);
lean_ctor_set(v___x_72_, 0, v_o_59_);
v___x_75_ = v___x_72_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_o_59_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_merged_70_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg___boxed(lean_object* v_o_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_80_, v___y_81_);
lean_dec(v___y_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object* v_o_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_o_84_, v___y_86_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___boxed(lean_object* v_o_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2(v_o_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object* v_e_94_, lean_object* v___y_95_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = l_Lean_Expr_hasMVar(v_e_94_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_e_94_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v_mctx_100_; lean_object* v___x_101_; lean_object* v_fst_102_; lean_object* v_snd_103_; lean_object* v___x_104_; lean_object* v_cache_105_; lean_object* v_zetaDeltaFVarIds_106_; lean_object* v_postponed_107_; lean_object* v_diag_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_117_; 
v___x_99_ = lean_st_ref_get(v___y_95_);
v_mctx_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_mctx_100_);
lean_dec(v___x_99_);
v___x_101_ = l_Lean_instantiateMVarsCore(v_mctx_100_, v_e_94_);
v_fst_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_fst_102_);
v_snd_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_snd_103_);
lean_dec_ref(v___x_101_);
v___x_104_ = lean_st_ref_take(v___y_95_);
v_cache_105_ = lean_ctor_get(v___x_104_, 1);
v_zetaDeltaFVarIds_106_ = lean_ctor_get(v___x_104_, 2);
v_postponed_107_ = lean_ctor_get(v___x_104_, 3);
v_diag_108_ = lean_ctor_get(v___x_104_, 4);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; 
v_unused_118_ = lean_ctor_get(v___x_104_, 0);
lean_dec(v_unused_118_);
v___x_110_ = v___x_104_;
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_diag_108_);
lean_inc(v_postponed_107_);
lean_inc(v_zetaDeltaFVarIds_106_);
lean_inc(v_cache_105_);
lean_dec(v___x_104_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_117_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v_snd_103_);
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_snd_103_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_cache_105_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_zetaDeltaFVarIds_106_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_postponed_107_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v_diag_108_);
v___x_113_ = v_reuseFailAlloc_116_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_st_ref_put(v___y_95_, v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v_fst_102_);
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object* v_e_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_e_119_, v___y_120_);
lean_dec(v___y_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object* v_e_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_e_123_, v___y_125_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object* v_e_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4(v_e_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(lean_object* v_hi_137_, lean_object* v_pivot_138_, lean_object* v_as_139_, lean_object* v_i_140_, lean_object* v_k_141_){
_start:
{
uint8_t v___x_142_; 
v___x_142_ = lean_nat_dec_lt(v_k_141_, v_hi_137_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec(v_k_141_);
v___x_143_ = lean_array_fswap(v_as_139_, v_i_140_, v_hi_137_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v_i_140_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v_fst_146_; lean_object* v_fst_147_; lean_object* v_start_148_; lean_object* v_start_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_145_ = lean_array_fget_borrowed(v_as_139_, v_k_141_);
v_fst_146_ = lean_ctor_get(v___x_145_, 0);
v_fst_147_ = lean_ctor_get(v_pivot_138_, 0);
v_start_148_ = lean_ctor_get(v_fst_146_, 0);
v_start_149_ = lean_ctor_get(v_fst_147_, 0);
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = lean_nat_add(v_start_148_, v___x_150_);
v___x_152_ = lean_nat_dec_le(v___x_151_, v_start_149_);
lean_dec(v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_nat_add(v_k_141_, v___x_150_);
lean_dec(v_k_141_);
v_k_141_ = v___x_153_;
goto _start;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_array_fswap(v_as_139_, v_i_140_, v_k_141_);
v___x_156_ = lean_nat_add(v_i_140_, v___x_150_);
lean_dec(v_i_140_);
v___x_157_ = lean_nat_add(v_k_141_, v___x_150_);
lean_dec(v_k_141_);
v_as_139_ = v___x_155_;
v_i_140_ = v___x_156_;
v_k_141_ = v___x_157_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg___boxed(lean_object* v_hi_159_, lean_object* v_pivot_160_, lean_object* v_as_161_, lean_object* v_i_162_, lean_object* v_k_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_159_, v_pivot_160_, v_as_161_, v_i_162_, v_k_163_);
lean_dec_ref(v_pivot_160_);
lean_dec(v_hi_159_);
return v_res_164_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(lean_object* v_x1_165_, lean_object* v_x2_166_){
_start:
{
lean_object* v_fst_167_; lean_object* v_fst_168_; lean_object* v_start_169_; lean_object* v_start_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_fst_167_ = lean_ctor_get(v_x1_165_, 0);
v_fst_168_ = lean_ctor_get(v_x2_166_, 0);
v_start_169_ = lean_ctor_get(v_fst_167_, 0);
v_start_170_ = lean_ctor_get(v_fst_168_, 0);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_start_169_, v___x_171_);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_start_170_);
lean_dec(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(lean_object* v_x1_174_, lean_object* v_x2_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v_x1_174_, v_x2_175_);
lean_dec_ref(v_x2_175_);
lean_dec_ref(v_x1_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(lean_object* v_n_178_, lean_object* v_as_179_, lean_object* v_lo_180_, lean_object* v_hi_181_){
_start:
{
lean_object* v___y_183_; uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_lt(v_lo_180_, v_hi_181_);
if (v___x_193_ == 0)
{
lean_dec(v_lo_180_);
return v_as_179_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_mid_196_; lean_object* v___y_198_; lean_object* v___y_204_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_194_ = lean_nat_add(v_lo_180_, v_hi_181_);
v___x_195_ = lean_unsigned_to_nat(1u);
v_mid_196_ = lean_nat_shiftr(v___x_194_, v___x_195_);
lean_dec(v___x_194_);
v___x_209_ = lean_array_fget_borrowed(v_as_179_, v_mid_196_);
v___x_210_ = lean_array_fget_borrowed(v_as_179_, v_lo_180_);
v___x_211_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
v___y_204_ = v_as_179_;
goto v___jp_203_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_array_fswap(v_as_179_, v_lo_180_, v_mid_196_);
v___y_204_ = v___x_212_;
goto v___jp_203_;
}
v___jp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = lean_array_fget_borrowed(v___y_198_, v_mid_196_);
v___x_200_ = lean_array_fget_borrowed(v___y_198_, v_hi_181_);
v___x_201_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_dec(v_mid_196_);
v___y_183_ = v___y_198_;
goto v___jp_182_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_fswap(v___y_198_, v_mid_196_, v_hi_181_);
lean_dec(v_mid_196_);
v___y_183_ = v___x_202_;
goto v___jp_182_;
}
}
v___jp_203_:
{
lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_205_ = lean_array_fget_borrowed(v___y_204_, v_hi_181_);
v___x_206_ = lean_array_fget_borrowed(v___y_204_, v_lo_180_);
v___x_207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_205_, v___x_206_);
if (v___x_207_ == 0)
{
v___y_198_ = v___y_204_;
goto v___jp_197_;
}
else
{
lean_object* v___x_208_; 
v___x_208_ = lean_array_fswap(v___y_204_, v_lo_180_, v_hi_181_);
v___y_198_ = v___x_208_;
goto v___jp_197_;
}
}
}
v___jp_182_:
{
lean_object* v_pivot_184_; lean_object* v___x_185_; lean_object* v_fst_186_; lean_object* v_snd_187_; uint8_t v___x_188_; 
v_pivot_184_ = lean_array_fget(v___y_183_, v_hi_181_);
lean_inc_n(v_lo_180_, 2);
v___x_185_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_181_, v_pivot_184_, v___y_183_, v_lo_180_, v_lo_180_);
lean_dec(v_pivot_184_);
v_fst_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_fst_186_);
v_snd_187_ = lean_ctor_get(v___x_185_, 1);
lean_inc(v_snd_187_);
lean_dec_ref(v___x_185_);
v___x_188_ = lean_nat_dec_le(v_hi_181_, v_fst_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_178_, v_snd_187_, v_lo_180_, v_fst_186_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_fst_186_, v___x_190_);
lean_dec(v_fst_186_);
v_as_179_ = v___x_189_;
v_lo_180_ = v___x_191_;
goto _start;
}
else
{
lean_dec(v_fst_186_);
lean_dec(v_lo_180_);
return v_snd_187_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(lean_object* v_n_213_, lean_object* v_as_214_, lean_object* v_lo_215_, lean_object* v_hi_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_213_, v_as_214_, v_lo_215_, v_hi_216_);
lean_dec(v_hi_216_);
lean_dec(v_n_213_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(uint8_t v_suppressElabErrors_219_, uint8_t v___y_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 1)
{
lean_object* v_pre_222_; 
v_pre_222_ = lean_ctor_get(v_x_221_, 0);
if (lean_obj_tag(v_pre_222_) == 0)
{
lean_object* v_str_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_str_223_ = lean_ctor_get(v_x_221_, 1);
v___x_224_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0));
v___x_225_ = lean_string_dec_eq(v_str_223_, v___x_224_);
if (v___x_225_ == 0)
{
return v___x_225_;
}
else
{
return v_suppressElabErrors_219_;
}
}
else
{
return v___y_220_;
}
}
else
{
return v___y_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed(lean_object* v_suppressElabErrors_226_, lean_object* v___y_227_, lean_object* v_x_228_){
_start:
{
uint8_t v_suppressElabErrors_boxed_229_; uint8_t v___y_18108__boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_suppressElabErrors_boxed_229_ = lean_unbox(v_suppressElabErrors_226_);
v___y_18108__boxed_230_ = lean_unbox(v___y_227_);
v_res_231_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v_suppressElabErrors_boxed_229_, v___y_18108__boxed_230_, v_x_228_);
lean_dec(v_x_228_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(lean_object* v_opts_233_, lean_object* v_opt_234_){
_start:
{
lean_object* v_name_235_; lean_object* v_defValue_236_; lean_object* v_map_237_; lean_object* v___x_238_; 
v_name_235_ = lean_ctor_get(v_opt_234_, 0);
v_defValue_236_ = lean_ctor_get(v_opt_234_, 1);
v_map_237_ = lean_ctor_get(v_opts_233_, 0);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_237_, v_name_235_);
if (lean_obj_tag(v___x_238_) == 0)
{
uint8_t v___x_239_; 
v___x_239_ = lean_unbox(v_defValue_236_);
return v___x_239_;
}
else
{
lean_object* v_val_240_; 
v_val_240_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_val_240_);
lean_dec_ref_known(v___x_238_, 1);
if (lean_obj_tag(v_val_240_) == 1)
{
uint8_t v_v_241_; 
v_v_241_ = lean_ctor_get_uint8(v_val_240_, 0);
lean_dec_ref_known(v_val_240_, 0);
return v_v_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec(v_val_240_);
v___x_242_ = lean_unbox(v_defValue_236_);
return v___x_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(lean_object* v_opts_243_, lean_object* v_opt_244_){
_start:
{
uint8_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_243_, v_opt_244_);
lean_dec_ref(v_opt_244_);
lean_dec_ref(v_opts_243_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_247_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v___x_251_);
lean_ctor_set(v___x_252_, 3, v___x_251_);
lean_ctor_set(v___x_252_, 4, v___x_250_);
lean_ctor_set(v___x_252_, 5, v___x_250_);
lean_ctor_set(v___x_252_, 6, v___x_250_);
lean_ctor_set(v___x_252_, 7, v___x_250_);
lean_ctor_set(v___x_252_, 8, v___x_250_);
lean_ctor_set(v___x_252_, 9, v___x_250_);
lean_ctor_set(v___x_252_, 10, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_unsigned_to_nat(32u);
v___x_254_ = lean_mk_empty_array_with_capacity(v___x_253_);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4(void){
_start:
{
size_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_256_ = ((size_t)5ULL);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_unsigned_to_nat(32u);
v___x_259_ = lean_mk_empty_array_with_capacity(v___x_258_);
v___x_260_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3);
v___x_261_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v___x_259_);
lean_ctor_set(v___x_261_, 2, v___x_257_);
lean_ctor_set(v___x_261_, 3, v___x_257_);
lean_ctor_set_usize(v___x_261_, 4, v___x_256_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_262_ = lean_box(1);
v___x_263_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4);
v___x_264_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
lean_ctor_set(v___x_265_, 2, v___x_262_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(lean_object* v_msgData_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v_env_270_; lean_object* v___x_271_; lean_object* v_scopes_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_opts_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_269_ = lean_st_ref_get(v___y_267_);
v_env_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_env_270_);
lean_dec(v___x_269_);
v___x_271_ = lean_st_ref_get(v___y_267_);
v_scopes_272_ = lean_ctor_get(v___x_271_, 2);
lean_inc(v_scopes_272_);
lean_dec(v___x_271_);
v___x_273_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_274_ = l_List_head_x21___redArg(v___x_273_, v_scopes_272_);
lean_dec(v_scopes_272_);
v_opts_275_ = lean_ctor_get(v___x_274_, 1);
lean_inc_ref(v_opts_275_);
lean_dec(v___x_274_);
v___x_276_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2);
v___x_277_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5);
v___x_278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_278_, 0, v_env_270_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
lean_ctor_set(v___x_278_, 2, v___x_277_);
lean_ctor_set(v___x_278_, 3, v_opts_275_);
v___x_279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_msgData_266_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_281_, v___y_282_);
lean_dec(v___y_282_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(lean_object* v_ref_286_, lean_object* v_msgData_287_, uint8_t v_severity_288_, uint8_t v_isSilent_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; uint8_t v___y_300_; lean_object* v___y_301_; uint8_t v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; uint8_t v___y_361_; lean_object* v___y_362_; uint8_t v___y_386_; uint8_t v___y_387_; lean_object* v___y_388_; uint8_t v___y_389_; lean_object* v___y_390_; uint8_t v___y_394_; uint8_t v___y_395_; uint8_t v___y_396_; uint8_t v___x_411_; uint8_t v___y_413_; uint8_t v___y_414_; uint8_t v___y_415_; uint8_t v___y_417_; uint8_t v___x_429_; 
v___x_411_ = 2;
v___x_429_ = l_Lean_instBEqMessageSeverity_beq(v_severity_288_, v___x_411_);
if (v___x_429_ == 0)
{
v___y_417_ = v___x_429_;
goto v___jp_416_;
}
else
{
uint8_t v___x_430_; 
lean_inc_ref(v_msgData_287_);
v___x_430_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_287_);
v___y_417_ = v___x_430_;
goto v___jp_416_;
}
v___jp_293_:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Elab_Command_getScope___redArg(v___y_301_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v___x_304_ = l_Lean_Elab_Command_getScope___redArg(v___y_301_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_340_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_340_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_340_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_340_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v_currNamespace_310_; lean_object* v_openDecls_311_; lean_object* v_env_312_; lean_object* v_messages_313_; lean_object* v_scopes_314_; lean_object* v_usedQuotCtxts_315_; lean_object* v_nextMacroScope_316_; lean_object* v_maxRecDepth_317_; lean_object* v_ngen_318_; lean_object* v_auxDeclNGen_319_; lean_object* v_infoState_320_; lean_object* v_traceState_321_; lean_object* v_snapshotTasks_322_; lean_object* v_prevLinterStates_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_339_; 
v___x_309_ = lean_st_ref_take(v___y_301_);
v_currNamespace_310_ = lean_ctor_get(v_a_303_, 2);
lean_inc(v_currNamespace_310_);
lean_dec(v_a_303_);
v_openDecls_311_ = lean_ctor_get(v_a_305_, 3);
lean_inc(v_openDecls_311_);
lean_dec(v_a_305_);
v_env_312_ = lean_ctor_get(v___x_309_, 0);
v_messages_313_ = lean_ctor_get(v___x_309_, 1);
v_scopes_314_ = lean_ctor_get(v___x_309_, 2);
v_usedQuotCtxts_315_ = lean_ctor_get(v___x_309_, 3);
v_nextMacroScope_316_ = lean_ctor_get(v___x_309_, 4);
v_maxRecDepth_317_ = lean_ctor_get(v___x_309_, 5);
v_ngen_318_ = lean_ctor_get(v___x_309_, 6);
v_auxDeclNGen_319_ = lean_ctor_get(v___x_309_, 7);
v_infoState_320_ = lean_ctor_get(v___x_309_, 8);
v_traceState_321_ = lean_ctor_get(v___x_309_, 9);
v_snapshotTasks_322_ = lean_ctor_get(v___x_309_, 10);
v_prevLinterStates_323_ = lean_ctor_get(v___x_309_, 11);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_339_ == 0)
{
v___x_325_ = v___x_309_;
v_isShared_326_ = v_isSharedCheck_339_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_prevLinterStates_323_);
lean_inc(v_snapshotTasks_322_);
lean_inc(v_traceState_321_);
lean_inc(v_infoState_320_);
lean_inc(v_auxDeclNGen_319_);
lean_inc(v_ngen_318_);
lean_inc(v_maxRecDepth_317_);
lean_inc(v_nextMacroScope_316_);
lean_inc(v_usedQuotCtxts_315_);
lean_inc(v_scopes_314_);
lean_inc(v_messages_313_);
lean_inc(v_env_312_);
lean_dec(v___x_309_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_339_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_currNamespace_310_);
lean_ctor_set(v___x_327_, 1, v_openDecls_311_);
v___x_328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___y_299_);
lean_inc_ref(v___y_297_);
lean_inc_ref(v___y_295_);
v___x_329_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_329_, 0, v___y_295_);
lean_ctor_set(v___x_329_, 1, v___y_298_);
lean_ctor_set(v___x_329_, 2, v___y_294_);
lean_ctor_set(v___x_329_, 3, v___y_297_);
lean_ctor_set(v___x_329_, 4, v___x_328_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*5, v___y_300_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*5 + 1, v___y_296_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*5 + 2, v_isSilent_289_);
v___x_330_ = l_Lean_MessageLog_add(v___x_329_, v_messages_313_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v___x_330_);
v___x_332_ = v___x_325_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_env_312_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v_scopes_314_);
lean_ctor_set(v_reuseFailAlloc_338_, 3, v_usedQuotCtxts_315_);
lean_ctor_set(v_reuseFailAlloc_338_, 4, v_nextMacroScope_316_);
lean_ctor_set(v_reuseFailAlloc_338_, 5, v_maxRecDepth_317_);
lean_ctor_set(v_reuseFailAlloc_338_, 6, v_ngen_318_);
lean_ctor_set(v_reuseFailAlloc_338_, 7, v_auxDeclNGen_319_);
lean_ctor_set(v_reuseFailAlloc_338_, 8, v_infoState_320_);
lean_ctor_set(v_reuseFailAlloc_338_, 9, v_traceState_321_);
lean_ctor_set(v_reuseFailAlloc_338_, 10, v_snapshotTasks_322_);
lean_ctor_set(v_reuseFailAlloc_338_, 11, v_prevLinterStates_323_);
v___x_332_ = v_reuseFailAlloc_338_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_333_ = lean_st_ref_put(v___y_301_, v___x_332_);
v___x_334_ = lean_box(0);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_334_);
v___x_336_ = v___x_307_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
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
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_303_);
lean_dec_ref(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_294_);
v_a_341_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_304_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_304_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_294_);
v_a_349_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_302_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_302_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
v___jp_357_:
{
lean_object* v_fileName_363_; lean_object* v_fileMap_364_; uint8_t v_suppressElabErrors_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_384_; 
v_fileName_363_ = lean_ctor_get(v___y_290_, 0);
v_fileMap_364_ = lean_ctor_get(v___y_290_, 1);
v_suppressElabErrors_365_ = lean_ctor_get_uint8(v___y_290_, sizeof(void*)*10);
v___x_366_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_287_);
v___x_367_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_366_, v___y_291_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_384_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_384_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_384_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc_ref_n(v_fileMap_364_, 2);
v___x_372_ = l_Lean_FileMap_toPosition(v_fileMap_364_, v___y_360_);
lean_dec(v___y_360_);
v___x_373_ = l_Lean_FileMap_toPosition(v_fileMap_364_, v___y_362_);
lean_dec(v___y_362_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___x_375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_365_ == 0)
{
lean_del_object(v___x_370_);
v___y_294_ = v___x_374_;
v___y_295_ = v_fileName_363_;
v___y_296_ = v___y_359_;
v___y_297_ = v___x_375_;
v___y_298_ = v___x_372_;
v___y_299_ = v_a_368_;
v___y_300_ = v___y_361_;
v___y_301_ = v___y_291_;
goto v___jp_293_;
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___f_378_; uint8_t v___x_379_; 
v___x_376_ = lean_box(v_suppressElabErrors_365_);
v___x_377_ = lean_box(v___y_358_);
v___f_378_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed), 3, 2);
lean_closure_set(v___f_378_, 0, v___x_376_);
lean_closure_set(v___f_378_, 1, v___x_377_);
lean_inc(v_a_368_);
v___x_379_ = l_Lean_MessageData_hasTag(v___f_378_, v_a_368_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec_ref_known(v___x_374_, 1);
lean_dec_ref(v___x_372_);
lean_dec(v_a_368_);
v___x_380_ = lean_box(0);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_380_);
v___x_382_ = v___x_370_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
else
{
lean_del_object(v___x_370_);
v___y_294_ = v___x_374_;
v___y_295_ = v_fileName_363_;
v___y_296_ = v___y_359_;
v___y_297_ = v___x_375_;
v___y_298_ = v___x_372_;
v___y_299_ = v_a_368_;
v___y_300_ = v___y_361_;
v___y_301_ = v___y_291_;
goto v___jp_293_;
}
}
}
}
v___jp_385_:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Syntax_getTailPos_x3f(v___y_388_, v___y_389_);
lean_dec(v___y_388_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_inc(v___y_390_);
v___y_358_ = v___y_386_;
v___y_359_ = v___y_387_;
v___y_360_ = v___y_390_;
v___y_361_ = v___y_389_;
v___y_362_ = v___y_390_;
goto v___jp_357_;
}
else
{
lean_object* v_val_392_; 
v_val_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_392_);
lean_dec_ref_known(v___x_391_, 1);
v___y_358_ = v___y_386_;
v___y_359_ = v___y_387_;
v___y_360_ = v___y_390_;
v___y_361_ = v___y_389_;
v___y_362_ = v_val_392_;
goto v___jp_357_;
}
}
v___jp_393_:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Elab_Command_getRef___redArg(v___y_290_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v_ref_399_; lean_object* v___x_400_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref_known(v___x_397_, 1);
v_ref_399_ = l_Lean_replaceRef(v_ref_286_, v_a_398_);
lean_dec(v_a_398_);
v___x_400_ = l_Lean_Syntax_getPos_x3f(v_ref_399_, v___y_395_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v___x_401_; 
v___x_401_ = lean_unsigned_to_nat(0u);
v___y_386_ = v___y_394_;
v___y_387_ = v___y_396_;
v___y_388_ = v_ref_399_;
v___y_389_ = v___y_395_;
v___y_390_ = v___x_401_;
goto v___jp_385_;
}
else
{
lean_object* v_val_402_; 
v_val_402_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v___x_400_, 1);
v___y_386_ = v___y_394_;
v___y_387_ = v___y_396_;
v___y_388_ = v_ref_399_;
v___y_389_ = v___y_395_;
v___y_390_ = v_val_402_;
goto v___jp_385_;
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec_ref(v_msgData_287_);
v_a_403_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_397_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_397_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
v___jp_412_:
{
if (v___y_415_ == 0)
{
v___y_394_ = v___y_413_;
v___y_395_ = v___y_414_;
v___y_396_ = v_severity_288_;
goto v___jp_393_;
}
else
{
v___y_394_ = v___y_413_;
v___y_395_ = v___y_414_;
v___y_396_ = v___x_411_;
goto v___jp_393_;
}
}
v___jp_416_:
{
if (v___y_417_ == 0)
{
lean_object* v___x_418_; lean_object* v_scopes_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_opts_422_; uint8_t v___x_423_; uint8_t v___x_424_; 
v___x_418_ = lean_st_ref_get(v___y_291_);
v_scopes_419_ = lean_ctor_get(v___x_418_, 2);
lean_inc(v_scopes_419_);
lean_dec(v___x_418_);
v___x_420_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_421_ = l_List_head_x21___redArg(v___x_420_, v_scopes_419_);
lean_dec(v_scopes_419_);
v_opts_422_ = lean_ctor_get(v___x_421_, 1);
lean_inc_ref(v_opts_422_);
lean_dec(v___x_421_);
v___x_423_ = 1;
v___x_424_ = l_Lean_instBEqMessageSeverity_beq(v_severity_288_, v___x_423_);
if (v___x_424_ == 0)
{
lean_dec_ref(v_opts_422_);
v___y_413_ = v___y_417_;
v___y_414_ = v___y_417_;
v___y_415_ = v___x_424_;
goto v___jp_412_;
}
else
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = l_Lean_warningAsError;
v___x_426_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_422_, v___x_425_);
lean_dec_ref(v_opts_422_);
v___y_413_ = v___y_417_;
v___y_414_ = v___y_417_;
v___y_415_ = v___x_426_;
goto v___jp_412_;
}
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec_ref(v_msgData_287_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object* v_ref_431_, lean_object* v_msgData_432_, lean_object* v_severity_433_, lean_object* v_isSilent_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v_severity_boxed_438_; uint8_t v_isSilent_boxed_439_; lean_object* v_res_440_; 
v_severity_boxed_438_ = lean_unbox(v_severity_433_);
v_isSilent_boxed_439_ = lean_unbox(v_isSilent_434_);
v_res_440_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_431_, v_msgData_432_, v_severity_boxed_438_, v_isSilent_boxed_439_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v_ref_431_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object* v_ref_441_, lean_object* v_msgData_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
uint8_t v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; 
v___x_446_ = 1;
v___x_447_ = 0;
v___x_448_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_441_, v_msgData_442_, v___x_446_, v___x_447_, v___y_443_, v___y_444_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object* v_ref_449_, lean_object* v_msgData_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_449_, v_msgData_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v_ref_449_);
return v_res_454_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* v_linterOption_461_, lean_object* v_stx_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_name_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_485_; 
v_name_467_ = lean_ctor_get(v_linterOption_461_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_linterOption_461_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_linterOption_461_, 1);
lean_dec(v_unused_486_);
v___x_469_ = v_linterOption_461_;
v_isShared_470_ = v_isSharedCheck_485_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_name_467_);
lean_dec(v_linterOption_461_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_485_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
lean_inc(v_name_467_);
v___x_472_ = l_Lean_MessageData_ofName(v_name_467_);
if (v_isShared_470_ == 0)
{
lean_ctor_set_tag(v___x_469_, 7);
lean_ctor_set(v___x_469_, 1, v___x_472_);
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_484_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_disable_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_475_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v_disable_477_ = l_Lean_MessageData_note(v___x_476_);
v___x_478_ = l_Lean_Linter_linterMessageTag;
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v_msg_463_);
lean_ctor_set(v___x_479_, 1, v_disable_477_);
v___x_480_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_478_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_481_, 0, v_name_467_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
lean_inc(v_stx_462_);
v___x_482_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_482_, 0, v_stx_462_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_462_, v___x_482_, v___y_464_, v___y_465_);
lean_dec(v_stx_462_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_487_, lean_object* v_stx_488_, lean_object* v_msg_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_487_, v_stx_488_, v_msg_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_508_ = l_Lean_stringToMessageData(v___x_507_);
return v___x_508_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_511_ = l_Lean_stringToMessageData(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_512_, size_t v_sz_513_, size_t v_i_514_, lean_object* v_b_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_lt(v_i_514_, v_sz_513_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v_b_515_);
return v___x_520_;
}
else
{
lean_object* v_a_521_; lean_object* v_snd_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_567_; 
v_a_521_ = lean_array_uget(v_as_512_, v_i_514_);
v_snd_522_ = lean_ctor_get(v_a_521_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_521_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_a_521_, 0);
lean_dec(v_unused_568_);
v___x_524_ = v_a_521_;
v_isShared_525_ = v_isSharedCheck_567_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_snd_522_);
lean_dec(v_a_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_567_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_snd_526_; lean_object* v_fst_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_566_; 
v_snd_526_ = lean_ctor_get(v_snd_522_, 1);
v_fst_527_ = lean_ctor_get(v_snd_522_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_snd_522_);
if (v_isSharedCheck_566_ == 0)
{
v___x_529_ = v_snd_522_;
v_isShared_530_ = v_isSharedCheck_566_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_snd_526_);
lean_inc(v_fst_527_);
lean_dec(v_snd_522_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_566_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_565_; 
v_fst_531_ = lean_ctor_get(v_snd_526_, 0);
v_snd_532_ = lean_ctor_get(v_snd_526_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_snd_526_);
if (v_isSharedCheck_565_ == 0)
{
v___x_534_ = v_snd_526_;
v_isShared_535_ = v_isSharedCheck_565_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_snd_532_);
lean_inc(v_fst_531_);
lean_dec(v_snd_526_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_565_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_536_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_538_ = l_Lean_MessageData_ofName(v_fst_531_);
lean_inc_ref(v___x_538_);
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 7);
lean_ctor_set(v___x_534_, 1, v___x_538_);
lean_ctor_set(v___x_534_, 0, v___x_537_);
v___x_540_ = v___x_534_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_564_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 7);
lean_ctor_set(v___x_529_, 1, v___x_541_);
lean_ctor_set(v___x_529_, 0, v___x_540_);
v___x_543_ = v___x_529_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_563_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = l_Lean_MessageData_ofName(v_snd_532_);
lean_inc_ref(v___x_544_);
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 7);
lean_ctor_set(v___x_524_, 1, v___x_544_);
lean_ctor_set(v___x_524_, 0, v___x_543_);
v___x_546_ = v___x_524_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_562_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_538_);
v___x_551_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v___x_544_);
v___x_554_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_548_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_536_, v_fst_527_, v___x_556_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; 
lean_dec_ref_known(v___x_557_, 1);
v___x_558_ = lean_box(0);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_514_, v___x_559_);
v_i_514_ = v___x_560_;
v_b_515_ = v___x_558_;
goto _start;
}
else
{
return v___x_557_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_569_, lean_object* v_sz_570_, lean_object* v_i_571_, lean_object* v_b_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
size_t v_sz_boxed_576_; size_t v_i_boxed_577_; lean_object* v_res_578_; 
v_sz_boxed_576_ = lean_unbox_usize(v_sz_570_);
lean_dec(v_sz_570_);
v_i_boxed_577_ = lean_unbox_usize(v_i_571_);
lean_dec(v_i_571_);
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_569_, v_sz_boxed_576_, v_i_boxed_577_, v_b_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_as_569_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_box(v___x_579_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v___x_18728__boxed_595_; lean_object* v_res_596_; 
v___x_18728__boxed_595_ = lean_unbox(v___x_588_);
v_res_596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_18728__boxed_595_, v_x_589_, v_x_590_, v_x_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_x_591_);
lean_dec_ref(v_x_590_);
lean_dec_ref(v_x_589_);
return v_res_596_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
uint8_t v___x_599_; 
v___x_599_ = 0;
return v___x_599_;
}
else
{
lean_object* v_key_600_; lean_object* v_tail_601_; uint8_t v___x_602_; 
v_key_600_ = lean_ctor_get(v_x_598_, 0);
v_tail_601_ = lean_ctor_get(v_x_598_, 2);
v___x_602_ = l_Lean_Syntax_instBEqRange_beq(v_key_600_, v_a_597_);
if (v___x_602_ == 0)
{
v_x_598_ = v_tail_601_;
goto _start;
}
else
{
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_604_, lean_object* v_x_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_604_, v_x_605_);
lean_dec(v_x_605_);
lean_dec_ref(v_a_604_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_buckets_610_; lean_object* v___x_611_; uint64_t v___x_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v_fold_615_; uint64_t v___x_616_; uint64_t v___x_617_; uint64_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_buckets_610_ = lean_ctor_get(v_m_608_, 1);
v___x_611_ = lean_array_get_size(v_buckets_610_);
v___x_612_ = l_Lean_Syntax_instHashableRange_hash(v_a_609_);
v___x_613_ = 32ULL;
v___x_614_ = lean_uint64_shift_right(v___x_612_, v___x_613_);
v_fold_615_ = lean_uint64_xor(v___x_612_, v___x_614_);
v___x_616_ = 16ULL;
v___x_617_ = lean_uint64_shift_right(v_fold_615_, v___x_616_);
v___x_618_ = lean_uint64_xor(v_fold_615_, v___x_617_);
v___x_619_ = lean_uint64_to_usize(v___x_618_);
v___x_620_ = lean_usize_of_nat(v___x_611_);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_sub(v___x_620_, v___x_621_);
v___x_623_ = lean_usize_land(v___x_619_, v___x_622_);
v___x_624_ = lean_array_uget_borrowed(v_buckets_610_, v___x_623_);
v___x_625_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_609_, v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_626_, lean_object* v_a_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_626_, v_a_627_);
lean_dec_ref(v_a_627_);
lean_dec_ref(v_m_626_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_dec(v_b_631_);
lean_dec_ref(v_a_630_);
return v_x_632_;
}
else
{
lean_object* v_key_633_; lean_object* v_value_634_; lean_object* v_tail_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
v_key_633_ = lean_ctor_get(v_x_632_, 0);
v_value_634_ = lean_ctor_get(v_x_632_, 1);
v_tail_635_ = lean_ctor_get(v_x_632_, 2);
v_isSharedCheck_647_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_647_ == 0)
{
v___x_637_ = v_x_632_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_tail_635_);
lean_inc(v_value_634_);
lean_inc(v_key_633_);
lean_dec(v_x_632_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
uint8_t v___x_639_; 
v___x_639_ = l_Lean_Syntax_instBEqRange_beq(v_key_633_, v_a_630_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_630_, v_b_631_, v_tail_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 2, v___x_640_);
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_key_633_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_value_634_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
else
{
lean_object* v___x_645_; 
lean_dec(v_value_634_);
lean_dec(v_key_633_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_b_631_);
lean_ctor_set(v___x_637_, 0, v_a_630_);
v___x_645_ = v___x_637_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_630_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_b_631_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_tail_635_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
return v_x_648_;
}
else
{
lean_object* v_key_650_; lean_object* v_value_651_; lean_object* v_tail_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_675_; 
v_key_650_ = lean_ctor_get(v_x_649_, 0);
v_value_651_ = lean_ctor_get(v_x_649_, 1);
v_tail_652_ = lean_ctor_get(v_x_649_, 2);
v_isSharedCheck_675_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_675_ == 0)
{
v___x_654_ = v_x_649_;
v_isShared_655_ = v_isSharedCheck_675_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_tail_652_);
lean_inc(v_value_651_);
lean_inc(v_key_650_);
lean_dec(v_x_649_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_675_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v_fold_660_; uint64_t v___x_661_; uint64_t v___x_662_; uint64_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_656_ = lean_array_get_size(v_x_648_);
v___x_657_ = l_Lean_Syntax_instHashableRange_hash(v_key_650_);
v___x_658_ = 32ULL;
v___x_659_ = lean_uint64_shift_right(v___x_657_, v___x_658_);
v_fold_660_ = lean_uint64_xor(v___x_657_, v___x_659_);
v___x_661_ = 16ULL;
v___x_662_ = lean_uint64_shift_right(v_fold_660_, v___x_661_);
v___x_663_ = lean_uint64_xor(v_fold_660_, v___x_662_);
v___x_664_ = lean_uint64_to_usize(v___x_663_);
v___x_665_ = lean_usize_of_nat(v___x_656_);
v___x_666_ = ((size_t)1ULL);
v___x_667_ = lean_usize_sub(v___x_665_, v___x_666_);
v___x_668_ = lean_usize_land(v___x_664_, v___x_667_);
v___x_669_ = lean_array_uget_borrowed(v_x_648_, v___x_668_);
lean_inc(v___x_669_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 2, v___x_669_);
v___x_671_ = v___x_654_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_key_650_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_value_651_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v___x_669_);
v___x_671_ = v_reuseFailAlloc_674_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_array_uset(v_x_648_, v___x_668_, v___x_671_);
v_x_648_ = v___x_672_;
v_x_649_ = v_tail_652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_676_, lean_object* v_source_677_, lean_object* v_target_678_){
_start:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_array_get_size(v_source_677_);
v___x_680_ = lean_nat_dec_lt(v_i_676_, v___x_679_);
if (v___x_680_ == 0)
{
lean_dec_ref(v_source_677_);
lean_dec(v_i_676_);
return v_target_678_;
}
else
{
lean_object* v_es_681_; lean_object* v___x_682_; lean_object* v_source_683_; lean_object* v_target_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_es_681_ = lean_array_fget(v_source_677_, v_i_676_);
v___x_682_ = lean_box(0);
v_source_683_ = lean_array_fset(v_source_677_, v_i_676_, v___x_682_);
v_target_684_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_678_, v_es_681_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_add(v_i_676_, v___x_685_);
lean_dec(v_i_676_);
v_i_676_ = v___x_686_;
v_source_677_ = v_source_683_;
v_target_678_ = v_target_684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_nbuckets_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_689_ = lean_array_get_size(v_data_688_);
v___x_690_ = lean_unsigned_to_nat(2u);
v_nbuckets_691_ = lean_nat_mul(v___x_689_, v___x_690_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_box(0);
v___x_694_ = lean_mk_array(v_nbuckets_691_, v___x_693_);
v___x_695_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_692_, v_data_688_, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_696_, lean_object* v_a_697_, lean_object* v_b_698_){
_start:
{
lean_object* v_size_699_; lean_object* v_buckets_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_743_; 
v_size_699_ = lean_ctor_get(v_m_696_, 0);
v_buckets_700_ = lean_ctor_get(v_m_696_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_m_696_);
if (v_isSharedCheck_743_ == 0)
{
v___x_702_ = v_m_696_;
v_isShared_703_ = v_isSharedCheck_743_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_buckets_700_);
lean_inc(v_size_699_);
lean_dec(v_m_696_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_743_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v_fold_708_; uint64_t v___x_709_; uint64_t v___x_710_; uint64_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; lean_object* v_bkt_717_; uint8_t v___x_718_; 
v___x_704_ = lean_array_get_size(v_buckets_700_);
v___x_705_ = l_Lean_Syntax_instHashableRange_hash(v_a_697_);
v___x_706_ = 32ULL;
v___x_707_ = lean_uint64_shift_right(v___x_705_, v___x_706_);
v_fold_708_ = lean_uint64_xor(v___x_705_, v___x_707_);
v___x_709_ = 16ULL;
v___x_710_ = lean_uint64_shift_right(v_fold_708_, v___x_709_);
v___x_711_ = lean_uint64_xor(v_fold_708_, v___x_710_);
v___x_712_ = lean_uint64_to_usize(v___x_711_);
v___x_713_ = lean_usize_of_nat(v___x_704_);
v___x_714_ = ((size_t)1ULL);
v___x_715_ = lean_usize_sub(v___x_713_, v___x_714_);
v___x_716_ = lean_usize_land(v___x_712_, v___x_715_);
v_bkt_717_ = lean_array_uget_borrowed(v_buckets_700_, v___x_716_);
v___x_718_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_697_, v_bkt_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v_size_x27_720_; lean_object* v___x_721_; lean_object* v_buckets_x27_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v_size_x27_720_ = lean_nat_add(v_size_699_, v___x_719_);
lean_dec(v_size_699_);
lean_inc(v_bkt_717_);
v___x_721_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_721_, 0, v_a_697_);
lean_ctor_set(v___x_721_, 1, v_b_698_);
lean_ctor_set(v___x_721_, 2, v_bkt_717_);
v_buckets_x27_722_ = lean_array_uset(v_buckets_700_, v___x_716_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(4u);
v___x_724_ = lean_nat_mul(v_size_x27_720_, v___x_723_);
v___x_725_ = lean_unsigned_to_nat(3u);
v___x_726_ = lean_nat_div(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_array_get_size(v_buckets_x27_722_);
v___x_728_ = lean_nat_dec_le(v___x_726_, v___x_727_);
lean_dec(v___x_726_);
if (v___x_728_ == 0)
{
lean_object* v_val_729_; lean_object* v___x_731_; 
v_val_729_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_722_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_val_729_);
lean_ctor_set(v___x_702_, 0, v_size_x27_720_);
v___x_731_ = v___x_702_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_size_x27_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_val_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v___x_734_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_buckets_x27_722_);
lean_ctor_set(v___x_702_, 0, v_size_x27_720_);
v___x_734_ = v___x_702_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_size_x27_720_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_buckets_x27_722_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
lean_object* v___x_736_; lean_object* v_buckets_x27_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
lean_inc(v_bkt_717_);
v___x_736_ = lean_box(0);
v_buckets_x27_737_ = lean_array_uset(v_buckets_700_, v___x_716_, v___x_736_);
v___x_738_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_697_, v_b_698_, v_bkt_717_);
v___x_739_ = lean_array_uset(v_buckets_x27_737_, v___x_716_, v___x_738_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___x_739_);
v___x_741_ = v___x_702_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_size_699_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_744_, lean_object* v_val_745_, lean_object* v_info_746_, lean_object* v___x_747_, lean_object* v_val_748_, uint8_t v___x_749_, lean_object* v_as_x27_750_, lean_object* v_b_751_, lean_object* v___y_752_){
_start:
{
if (lean_obj_tag(v_as_x27_750_) == 0)
{
lean_object* v___x_754_; 
lean_dec_ref(v_val_748_);
lean_dec(v___x_747_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_b_751_);
return v___x_754_;
}
else
{
lean_object* v_head_755_; lean_object* v_tail_756_; lean_object* v___x_757_; lean_object* v_env_758_; lean_object* v___x_759_; lean_object* v___x_772_; 
v_head_755_ = lean_ctor_get(v_as_x27_750_, 0);
v_tail_756_ = lean_ctor_get(v_as_x27_750_, 1);
v___x_757_ = lean_st_ref_get(v___y_752_);
v_env_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc_ref(v_env_758_);
lean_dec(v___x_757_);
v___x_759_ = lean_box(0);
lean_inc(v_head_755_);
v___x_772_ = l_Lean_Environment_find_x3f(v_env_758_, v_head_755_, v___x_749_);
if (lean_obj_tag(v___x_772_) == 1)
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_772_, 1);
if (lean_obj_tag(v_val_773_) == 6)
{
lean_object* v_val_774_; lean_object* v_numFields_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_val_774_ = lean_ctor_get(v_val_773_, 0);
lean_inc_ref(v_val_774_);
lean_dec_ref_known(v_val_773_, 1);
v_numFields_775_ = lean_ctor_get(v_val_774_, 4);
lean_inc(v_numFields_775_);
lean_dec_ref(v_val_774_);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_nat_dec_lt(v___x_776_, v_numFields_775_);
lean_dec(v_numFields_775_);
if (v___x_777_ == 0)
{
goto v___jp_760_;
}
else
{
v_as_x27_750_ = v_tail_756_;
v_b_751_ = v___x_759_;
goto _start;
}
}
else
{
lean_dec(v_val_773_);
goto v___jp_760_;
}
}
else
{
lean_dec(v___x_772_);
goto v___jp_760_;
}
v___jp_760_:
{
if (lean_obj_tag(v_head_755_) == 1)
{
lean_object* v_str_761_; uint8_t v___x_762_; 
v_str_761_ = lean_ctor_get(v_head_755_, 1);
v___x_762_ = lean_string_dec_eq(v_str_761_, v_str_744_);
if (v___x_762_ == 0)
{
v_as_x27_750_ = v_tail_756_;
v_b_751_ = v___x_759_;
goto _start;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_764_ = lean_st_ref_take(v_val_745_);
v___x_765_ = l_Lean_Elab_Info_stx(v_info_746_);
lean_inc_ref(v_head_755_);
lean_inc(v___x_747_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_747_);
lean_ctor_set(v___x_766_, 1, v_head_755_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
lean_inc_ref(v_val_748_);
v___x_768_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_764_, v_val_748_, v___x_767_);
v___x_769_ = lean_st_ref_put(v_val_745_, v___x_768_);
v_as_x27_750_ = v_tail_756_;
v_b_751_ = v___x_759_;
goto _start;
}
}
else
{
v_as_x27_750_ = v_tail_756_;
v_b_751_ = v___x_759_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_779_, lean_object* v_val_780_, lean_object* v_info_781_, lean_object* v___x_782_, lean_object* v_val_783_, lean_object* v___x_784_, lean_object* v_as_x27_785_, lean_object* v_b_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v___x_18992__boxed_789_; lean_object* v_res_790_; 
v___x_18992__boxed_789_ = lean_unbox(v___x_784_);
v_res_790_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_779_, v_val_780_, v_info_781_, v___x_782_, v_val_783_, v___x_18992__boxed_789_, v_as_x27_785_, v_b_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec(v_as_x27_785_);
lean_dec_ref(v_info_781_);
lean_dec(v_val_780_);
lean_dec_ref(v_str_779_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_791_, v___y_793_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = lean_whnf(v_a_798_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_799_;
}
else
{
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_807_, lean_object* v___x_808_, lean_object* v_val_809_, lean_object* v___x_810_, lean_object* v_ci_811_, lean_object* v_info_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
if (lean_obj_tag(v_info_812_) == 1)
{
lean_object* v_i_817_; lean_object* v_expr_818_; 
v_i_817_ = lean_ctor_get(v_info_812_, 0);
v_expr_818_ = lean_ctor_get(v_i_817_, 3);
if (lean_obj_tag(v_expr_818_) == 1)
{
lean_object* v_lctx_819_; lean_object* v_expectedType_x3f_820_; uint8_t v_isBinder_821_; lean_object* v_fvarId_822_; lean_object* v___x_823_; 
v_lctx_819_ = lean_ctor_get(v_i_817_, 1);
v_expectedType_x3f_820_ = lean_ctor_get(v_i_817_, 2);
v_isBinder_821_ = lean_ctor_get_uint8(v_i_817_, sizeof(void*)*4);
v_fvarId_822_ = lean_ctor_get(v_expr_818_, 0);
v___x_823_ = l_Lean_Elab_Info_range_x3f(v_info_812_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_979_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_979_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_979_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_979_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_st_ref_get(v_val_807_);
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_828_, v_val_824_);
lean_dec(v___x_828_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = l_Lean_Elab_Info_stx(v_info_812_);
v___x_831_ = l_Lean_Syntax_getHeadInfo(v___x_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 4);
if (v_isBinder_821_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v___x_830_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_808_);
v___x_833_ = v___x_826_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_808_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
else
{
lean_object* v___x_835_; 
lean_inc(v_fvarId_822_);
lean_inc_ref(v_lctx_819_);
v___x_835_ = lean_local_ctx_find(v_lctx_819_, v_fvarId_822_);
if (lean_obj_tag(v___x_835_) == 1)
{
lean_object* v_val_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_969_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_969_ == 0)
{
v___x_838_ = v___x_835_;
v_isShared_839_ = v_isSharedCheck_969_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_val_836_);
lean_dec(v___x_835_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_969_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_start_840_; uint8_t v___x_841_; 
v_start_840_ = lean_ctor_get(v_val_824_, 0);
v___x_841_ = l_Lean_Syntax_Range_contains(v_val_809_, v_start_840_, v___x_829_);
if (v___x_841_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v_val_836_);
lean_dec(v___x_830_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 0);
lean_ctor_set(v___x_838_, 0, v___x_808_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_808_);
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
if (v___x_829_ == 0)
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = l_Lean_LocalDecl_userName(v_val_836_);
lean_dec(v_val_836_);
v___x_846_ = l_Lean_Name_hasMacroScopes(v___x_845_);
lean_dec(v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v_toCommandContextInfo_847_; lean_object* v_options_848_; lean_object* v___x_849_; 
v_toCommandContextInfo_847_ = lean_ctor_get(v_ci_811_, 0);
v_options_848_ = lean_ctor_get(v_toCommandContextInfo_847_, 4);
lean_inc_ref(v_options_848_);
v___x_849_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_848_, v___y_815_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_954_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_954_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_954_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_954_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_Linter_getLinterValue(v___x_810_, v_a_850_);
lean_dec(v_a_850_);
if (v___x_854_ == 0)
{
lean_object* v___x_856_; 
lean_del_object(v___x_838_);
lean_dec(v___x_830_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_808_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_808_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Syntax_getId(v___x_830_);
lean_dec(v___x_830_);
if (lean_obj_tag(v___x_858_) == 1)
{
lean_object* v_pre_859_; lean_object* v_str_860_; lean_object* v_ty_862_; lean_object* v___y_863_; lean_object* v___y_864_; 
v_pre_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_pre_859_);
v_str_860_ = lean_ctor_get(v___x_858_, 1);
lean_inc_ref(v_str_860_);
if (lean_obj_tag(v_pre_859_) == 0)
{
lean_del_object(v___x_852_);
if (lean_obj_tag(v_expectedType_x3f_820_) == 1)
{
lean_object* v_val_921_; 
lean_del_object(v___x_826_);
v_val_921_ = lean_ctor_get(v_expectedType_x3f_820_, 0);
lean_inc(v_val_921_);
v_ty_862_ = v_val_921_;
v___y_863_ = v___y_814_;
v___y_864_ = v___y_815_;
goto v___jp_861_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_inc_ref(v_expr_818_);
v___x_922_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_922_, 0, v_expr_818_);
lean_inc_ref(v_ci_811_);
lean_inc_ref(v_i_817_);
v___x_923_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_817_, v_ci_811_, v___x_922_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
lean_del_object(v___x_826_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v_ty_862_ = v_a_924_;
v___y_863_ = v___y_814_;
v___y_864_ = v___y_815_;
goto v___jp_861_;
}
else
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v_str_860_);
lean_dec_ref_known(v___x_858_, 2);
lean_del_object(v___x_838_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
v_isSharedCheck_945_ = !lean_is_exclusive(v_val_824_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; lean_object* v_unused_947_; 
v_unused_946_ = lean_ctor_get(v_val_824_, 1);
lean_dec(v_unused_946_);
v_unused_947_ = lean_ctor_get(v_val_824_, 0);
lean_dec(v_unused_947_);
v___x_926_ = v_val_824_;
v_isShared_927_ = v_isSharedCheck_945_;
goto v_resetjp_925_;
}
else
{
lean_dec(v_val_824_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_945_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_944_; 
v_a_928_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_944_ == 0)
{
v___x_930_ = v___x_923_;
v_isShared_931_ = v_isSharedCheck_944_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_923_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_944_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_ref_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v_ref_932_ = lean_ctor_get(v___y_814_, 7);
v___x_933_ = lean_io_error_to_string(v_a_928_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 3);
lean_ctor_set(v___x_826_, 0, v___x_933_);
v___x_935_ = v___x_826_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_943_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_MessageData_ofFormat(v___x_935_);
lean_inc(v_ref_932_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_936_);
lean_ctor_set(v___x_926_, 0, v_ref_932_);
v___x_938_ = v___x_926_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_ref_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_936_);
v___x_938_ = v_reuseFailAlloc_942_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_940_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_938_);
v___x_940_ = v___x_930_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
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
lean_object* v___x_949_; 
lean_dec_ref(v_str_860_);
lean_dec(v_pre_859_);
lean_dec_ref_known(v___x_858_, 2);
lean_del_object(v___x_838_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_808_);
v___x_949_ = v___x_852_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_808_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
v___jp_861_:
{
lean_object* v___f_865_; lean_object* v___x_866_; 
v___f_865_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_865_, 0, v_ty_862_);
lean_inc_ref(v_i_817_);
v___x_866_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_817_, v_ci_811_, v___f_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_897_; 
lean_del_object(v___x_838_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_897_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_897_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_897_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Expr_getAppFn_x27(v_a_867_);
lean_dec(v_a_867_);
if (lean_obj_tag(v___x_871_) == 4)
{
lean_object* v_declName_872_; lean_object* v___x_873_; lean_object* v_env_874_; lean_object* v___x_875_; 
v_declName_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_declName_872_);
lean_dec_ref_known(v___x_871_, 2);
v___x_873_ = lean_st_ref_get(v___y_864_);
v_env_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc_ref(v_env_874_);
lean_dec(v___x_873_);
v___x_875_ = l_Lean_Environment_find_x3f(v_env_874_, v_declName_872_, v___x_829_);
if (lean_obj_tag(v___x_875_) == 1)
{
lean_object* v_val_876_; 
v_val_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_val_876_);
lean_dec_ref_known(v___x_875_, 1);
if (lean_obj_tag(v_val_876_) == 5)
{
lean_object* v_val_877_; lean_object* v_ctors_878_; lean_object* v___x_879_; 
lean_del_object(v___x_869_);
v_val_877_ = lean_ctor_get(v_val_876_, 0);
lean_inc_ref(v_val_877_);
lean_dec_ref_known(v_val_876_, 1);
v_ctors_878_ = lean_ctor_get(v_val_877_, 4);
lean_inc(v_ctors_878_);
lean_dec_ref(v_val_877_);
v___x_879_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_860_, v_val_807_, v_info_812_, v___x_858_, v_val_824_, v___x_829_, v_ctors_878_, v___x_808_, v___y_864_);
lean_dec(v_ctors_878_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_str_860_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_879_, 0);
lean_dec(v_unused_887_);
v___x_881_ = v___x_879_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_879_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_808_);
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_808_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
return v___x_879_;
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v_val_876_);
lean_dec_ref(v_str_860_);
lean_dec_ref_known(v___x_858_, 2);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_808_);
v___x_889_ = v___x_869_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_808_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v___x_875_);
lean_dec_ref(v_str_860_);
lean_dec_ref_known(v___x_858_, 2);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_808_);
v___x_892_ = v___x_869_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_808_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec_ref(v___x_871_);
lean_dec_ref(v_str_860_);
lean_dec_ref_known(v___x_858_, 2);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_808_);
v___x_895_ = v___x_869_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_808_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_str_860_);
lean_dec_ref_known(v___x_858_, 2);
lean_dec_ref_known(v_info_812_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_val_824_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_919_ = lean_ctor_get(v_val_824_, 1);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_val_824_, 0);
lean_dec(v_unused_920_);
v___x_899_ = v_val_824_;
v_isShared_900_ = v_isSharedCheck_918_;
goto v_resetjp_898_;
}
else
{
lean_dec(v_val_824_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_918_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_917_; 
v_a_901_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_917_ == 0)
{
v___x_903_ = v___x_866_;
v_isShared_904_ = v_isSharedCheck_917_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_866_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_917_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v_ref_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v_ref_905_ = lean_ctor_get(v___y_863_, 7);
v___x_906_ = lean_io_error_to_string(v_a_901_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 3);
lean_ctor_set(v___x_838_, 0, v___x_906_);
v___x_908_ = v___x_838_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_916_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_MessageData_ofFormat(v___x_908_);
lean_inc(v_ref_905_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v___x_909_);
lean_ctor_set(v___x_899_, 0, v_ref_905_);
v___x_911_ = v___x_899_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_ref_905_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_909_);
v___x_911_ = v_reuseFailAlloc_915_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_911_);
v___x_913_ = v___x_903_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
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
}
}
}
else
{
lean_object* v___x_952_; 
lean_dec(v___x_858_);
lean_del_object(v___x_838_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_808_);
v___x_952_ = v___x_852_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_808_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_838_);
lean_dec(v___x_830_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
v_a_955_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_849_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_849_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_964_; 
lean_dec(v___x_830_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 0);
lean_ctor_set(v___x_838_, 0, v___x_808_);
v___x_964_ = v___x_838_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_808_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v___x_967_; 
lean_dec(v_val_836_);
lean_dec(v___x_830_);
lean_del_object(v___x_826_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_839_ == 0)
{
lean_ctor_set_tag(v___x_838_, 0);
lean_ctor_set(v___x_838_, 0, v___x_808_);
v___x_967_ = v___x_838_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_808_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v___x_835_);
lean_dec(v___x_830_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_808_);
v___x_971_ = v___x_826_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_808_);
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
lean_object* v___x_974_; 
lean_dec(v___x_831_);
lean_dec(v___x_830_);
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_808_);
v___x_974_ = v___x_826_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_808_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
lean_object* v___x_977_; 
lean_dec(v_val_824_);
lean_dec_ref_known(v_info_812_, 1);
lean_dec_ref(v_ci_811_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_808_);
v___x_977_ = v___x_826_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_808_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v___x_823_);
lean_dec_ref(v_ci_811_);
v_isSharedCheck_986_ = !lean_is_exclusive(v_info_812_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; 
v_unused_987_ = lean_ctor_get(v_info_812_, 0);
lean_dec(v_unused_987_);
v___x_981_ = v_info_812_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_dec(v_info_812_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set_tag(v___x_981_, 0);
lean_ctor_set(v___x_981_, 0, v___x_808_);
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_808_);
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
lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_ci_811_);
v_isSharedCheck_994_ = !lean_is_exclusive(v_info_812_);
if (v_isSharedCheck_994_ == 0)
{
lean_object* v_unused_995_; 
v_unused_995_ = lean_ctor_get(v_info_812_, 0);
lean_dec(v_unused_995_);
v___x_989_ = v_info_812_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_dec(v_info_812_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 0);
lean_ctor_set(v___x_989_, 0, v___x_808_);
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_808_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v___x_996_; 
lean_dec_ref(v_info_812_);
lean_dec_ref(v_ci_811_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_808_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_997_, lean_object* v___x_998_, lean_object* v_val_999_, lean_object* v___x_1000_, lean_object* v_ci_1001_, lean_object* v_info_1002_, lean_object* v_x_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_997_, v___x_998_, v_val_999_, v___x_1000_, v_ci_1001_, v_info_1002_, v_x_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec_ref(v_x_1003_);
lean_dec_ref(v___x_1000_);
lean_dec_ref(v_val_999_);
lean_dec(v_val_997_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_1008_, lean_object* v_ci_1009_, lean_object* v_i_1010_, lean_object* v_cs_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
v___x_1016_ = lean_apply_6(v_postNode_1008_, v_ci_1009_, v_i_1010_, v_cs_1011_, v___y_1013_, v___y_1014_, lean_box(0));
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1017_, lean_object* v_ci_1018_, lean_object* v_i_1019_, lean_object* v_cs_1020_, lean_object* v_x_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1017_, v_ci_1018_, v_i_1019_, v_cs_1020_, v_x_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v_x_1021_);
return v_res_1025_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_instMonadEIO(lean_box(0));
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_toApplicative_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1066_; 
v___x_1033_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1034_ = l_StateRefT_x27_instMonad___redArg(v___x_1033_);
v_toApplicative_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_1034_, 1);
lean_dec(v_unused_1067_);
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1066_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_toApplicative_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1066_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_toFunctor_1039_; lean_object* v_toSeq_1040_; lean_object* v_toSeqLeft_1041_; lean_object* v_toSeqRight_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1064_; 
v_toFunctor_1039_ = lean_ctor_get(v_toApplicative_1035_, 0);
v_toSeq_1040_ = lean_ctor_get(v_toApplicative_1035_, 2);
v_toSeqLeft_1041_ = lean_ctor_get(v_toApplicative_1035_, 3);
v_toSeqRight_1042_ = lean_ctor_get(v_toApplicative_1035_, 4);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_toApplicative_1035_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_toApplicative_1035_, 1);
lean_dec(v_unused_1065_);
v___x_1044_ = v_toApplicative_1035_;
v_isShared_1045_ = v_isSharedCheck_1064_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_toSeqRight_1042_);
lean_inc(v_toSeqLeft_1041_);
lean_inc(v_toSeq_1040_);
lean_inc(v_toFunctor_1039_);
lean_dec(v_toApplicative_1035_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1064_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1055_; 
v___f_1046_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1047_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1039_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toFunctor_1039_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toFunctor_1039_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___f_1048_);
lean_ctor_set(v___x_1050_, 1, v___f_1049_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toSeqRight_1042_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toSeqLeft_1041_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toSeq_1040_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 4, v___f_1051_);
lean_ctor_set(v___x_1044_, 3, v___f_1052_);
lean_ctor_set(v___x_1044_, 2, v___f_1053_);
lean_ctor_set(v___x_1044_, 1, v___f_1046_);
lean_ctor_set(v___x_1044_, 0, v___x_1050_);
v___x_1055_ = v___x_1044_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___f_1046_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___f_1053_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v___f_1052_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___f_1051_);
v___x_1055_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___f_1047_);
lean_ctor_set(v___x_1037_, 0, v___x_1055_);
v___x_1057_ = v___x_1037_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___f_1047_);
v___x_1057_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_15151__overap_1060_; lean_object* v___x_1061_; 
v___x_1058_ = lean_box(0);
v___x_1059_ = l_instInhabitedOfMonad___redArg(v___x_1057_, v___x_1058_);
v___x_15151__overap_1060_ = lean_panic_fn_borrowed(v___x_1059_, v_msg_1029_);
lean_dec(v___x_1059_);
lean_inc(v___y_1031_);
lean_inc_ref(v___y_1030_);
v___x_1061_ = lean_apply_3(v___x_15151__overap_1060_, v___y_1030_, v___y_1031_, lean_box(0));
return v___x_1061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1072_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1077_ = lean_unsigned_to_nat(21u);
v___x_1078_ = lean_unsigned_to_nat(65u);
v___x_1079_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1080_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1081_ = l_mkPanicMessageWithDecl(v___x_1080_, v___x_1079_, v___x_1078_, v___x_1077_, v___x_1076_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1082_, lean_object* v_postNode_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
switch(lean_obj_tag(v_x_1085_))
{
case 0:
{
lean_object* v_i_1089_; lean_object* v_t_1090_; lean_object* v___x_1091_; 
v_i_1089_ = lean_ctor_get(v_x_1085_, 0);
lean_inc_ref(v_i_1089_);
v_t_1090_ = lean_ctor_get(v_x_1085_, 1);
lean_inc_ref(v_t_1090_);
lean_dec_ref_known(v_x_1085_, 2);
v___x_1091_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1089_, v_x_1084_);
v_x_1084_ = v___x_1091_;
v_x_1085_ = v_t_1090_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1084_) == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec_ref_known(v_x_1085_, 2);
lean_dec_ref(v_postNode_1083_);
lean_dec_ref(v_preNode_1082_);
v___x_1093_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1094_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1093_, v___y_1086_, v___y_1087_);
return v___x_1094_;
}
else
{
lean_object* v_i_1095_; lean_object* v_children_1096_; lean_object* v_val_1097_; lean_object* v___x_1098_; 
v_i_1095_ = lean_ctor_get(v_x_1085_, 0);
lean_inc_ref_n(v_i_1095_, 2);
v_children_1096_ = lean_ctor_get(v_x_1085_, 1);
lean_inc_ref_n(v_children_1096_, 2);
lean_dec_ref_known(v_x_1085_, 2);
v_val_1097_ = lean_ctor_get(v_x_1084_, 0);
lean_inc_n(v_val_1097_, 2);
lean_inc_ref(v_preNode_1082_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
v___x_1098_ = lean_apply_6(v_preNode_1082_, v_val_1097_, v_i_1095_, v_children_1096_, v___y_1086_, v___y_1087_, lean_box(0));
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; uint8_t v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = lean_unbox(v_a_1099_);
lean_dec(v_a_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1125_; 
lean_dec_ref(v_preNode_1082_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1084_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_x_1084_, 0);
lean_dec(v_unused_1126_);
v___x_1102_ = v_x_1084_;
v_isShared_1103_ = v_isSharedCheck_1125_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_x_1084_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1125_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_box(0);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
v___x_1105_ = lean_apply_7(v_postNode_1083_, v_val_1097_, v_i_1095_, v_children_1096_, v___x_1104_, v___y_1086_, v___y_1087_, lean_box(0));
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1116_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_a_1106_);
v___x_1111_ = v___x_1102_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1102_);
v_a_1117_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1105_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1105_);
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
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1127_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1084_, v_i_1095_);
v___x_1128_ = l_Lean_PersistentArray_toList___redArg(v_children_1096_);
v___x_1129_ = lean_box(0);
lean_inc_ref(v_postNode_1083_);
v___x_1130_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1082_, v_postNode_1083_, v___x_1127_, v___x_1128_, v___x_1129_, v___y_1086_, v___y_1087_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1086_);
v___x_1132_ = lean_apply_7(v_postNode_1083_, v_val_1097_, v_i_1095_, v_children_1096_, v_a_1131_, v___y_1086_, v___y_1087_, lean_box(0));
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v_a_1133_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
v_a_1142_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1132_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1132_);
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
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec(v_val_1097_);
lean_dec_ref(v_children_1096_);
lean_dec_ref(v_i_1095_);
lean_dec_ref(v_postNode_1083_);
v_a_1150_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1130_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1130_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_val_1097_);
lean_dec_ref(v_children_1096_);
lean_dec_ref_known(v_x_1084_, 1);
lean_dec_ref(v_i_1095_);
lean_dec_ref(v_postNode_1083_);
lean_dec_ref(v_preNode_1082_);
v_a_1158_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1098_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1098_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
default: 
{
lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
lean_dec(v_x_1084_);
lean_dec_ref(v_postNode_1083_);
lean_dec_ref(v_preNode_1082_);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_x_1085_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; 
v_unused_1174_ = lean_ctor_get(v_x_1085_, 0);
lean_dec(v_unused_1174_);
v___x_1167_ = v_x_1085_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_dec(v_x_1085_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_box(0);
if (v_isShared_1168_ == 0)
{
lean_ctor_set_tag(v___x_1167_, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1175_, lean_object* v_postNode_1176_, lean_object* v___x_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
if (lean_obj_tag(v_x_1178_) == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
lean_dec(v___x_1177_);
lean_dec_ref(v_postNode_1176_);
lean_dec_ref(v_preNode_1175_);
v___x_1183_ = l_List_reverse___redArg(v_x_1179_);
v___x_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
return v___x_1184_;
}
else
{
lean_object* v_head_1185_; lean_object* v_tail_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1204_; 
v_head_1185_ = lean_ctor_get(v_x_1178_, 0);
v_tail_1186_ = lean_ctor_get(v_x_1178_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_x_1178_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1188_ = v_x_1178_;
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_tail_1186_);
lean_inc(v_head_1185_);
lean_dec(v_x_1178_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1204_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; 
lean_inc(v___x_1177_);
lean_inc_ref(v_postNode_1176_);
lean_inc_ref(v_preNode_1175_);
v___x_1190_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1175_, v_postNode_1176_, v___x_1177_, v_head_1185_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v_x_1179_);
lean_ctor_set(v___x_1188_, 0, v_a_1191_);
v___x_1193_ = v___x_1188_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1191_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_x_1179_);
v___x_1193_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
v_x_1178_ = v_tail_1186_;
v_x_1179_ = v___x_1193_;
goto _start;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1188_);
lean_dec(v_tail_1186_);
lean_dec(v_x_1179_);
lean_dec(v___x_1177_);
lean_dec_ref(v_postNode_1176_);
lean_dec_ref(v_preNode_1175_);
v_a_1196_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1190_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1190_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1205_, lean_object* v_postNode_1206_, lean_object* v___x_1207_, lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1205_, v_postNode_1206_, v___x_1207_, v_x_1208_, v_x_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1214_, lean_object* v_postNode_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1214_, v_postNode_1215_, v_x_1216_, v_x_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1222_, lean_object* v_postNode_1223_, lean_object* v_ctx_x3f_1224_, lean_object* v_t_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1229_, 0, v_postNode_1223_);
v___x_1230_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1222_, v___f_1229_, v_ctx_x3f_1224_, v_t_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1230_, 0);
lean_dec(v_unused_1239_);
v___x_1232_ = v___x_1230_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v___x_1230_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_box(0);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
v_a_1240_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1230_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1230_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1248_, lean_object* v_postNode_1249_, lean_object* v_ctx_x3f_1250_, lean_object* v_t_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1248_, v_postNode_1249_, v_ctx_x3f_1250_, v_t_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1256_, lean_object* v_val_1257_, lean_object* v_val_1258_, lean_object* v_as_1259_, size_t v_sz_1260_, size_t v_i_1261_, lean_object* v_b_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1261_, v_sz_1260_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_val_1258_);
lean_dec(v_val_1257_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1262_);
return v___x_1267_;
}
else
{
lean_object* v___x_1268_; lean_object* v___f_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___f_1272_; lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1268_ = lean_box(v___x_1256_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1269_, 0, v___x_1268_);
v___x_1270_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1271_ = lean_box(0);
lean_inc_ref(v_val_1258_);
lean_inc(v_val_1257_);
v___f_1272_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1272_, 0, v_val_1257_);
lean_closure_set(v___f_1272_, 1, v___x_1271_);
lean_closure_set(v___f_1272_, 2, v_val_1258_);
lean_closure_set(v___f_1272_, 3, v___x_1270_);
v_a_1273_ = lean_array_uget_borrowed(v_as_1259_, v_i_1261_);
v___x_1274_ = lean_box(0);
lean_inc(v_a_1273_);
v___x_1275_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1269_, v___f_1272_, v___x_1274_, v_a_1273_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1275_) == 0)
{
size_t v___x_1276_; size_t v___x_1277_; 
lean_dec_ref_known(v___x_1275_, 1);
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1261_, v___x_1276_);
v_i_1261_ = v___x_1277_;
v_b_1262_ = v___x_1271_;
goto _start;
}
else
{
lean_dec_ref(v_val_1258_);
lean_dec(v_val_1257_);
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1279_, lean_object* v_val_1280_, lean_object* v_val_1281_, lean_object* v_as_1282_, lean_object* v_sz_1283_, lean_object* v_i_1284_, lean_object* v_b_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
uint8_t v___x_19856__boxed_1289_; size_t v_sz_boxed_1290_; size_t v_i_boxed_1291_; lean_object* v_res_1292_; 
v___x_19856__boxed_1289_ = lean_unbox(v___x_1279_);
v_sz_boxed_1290_ = lean_unbox_usize(v_sz_1283_);
lean_dec(v_sz_1283_);
v_i_boxed_1291_ = lean_unbox_usize(v_i_1284_);
lean_dec(v_i_1284_);
v_res_1292_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_19856__boxed_1289_, v_val_1280_, v_val_1281_, v_as_1282_, v_sz_boxed_1290_, v_i_boxed_1291_, v_b_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v_as_1282_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1293_, lean_object* v_x_1294_){
_start:
{
if (lean_obj_tag(v_x_1294_) == 0)
{
return v_x_1293_;
}
else
{
lean_object* v_key_1295_; lean_object* v_value_1296_; lean_object* v_tail_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v_key_1295_ = lean_ctor_get(v_x_1294_, 0);
v_value_1296_ = lean_ctor_get(v_x_1294_, 1);
v_tail_1297_ = lean_ctor_get(v_x_1294_, 2);
lean_inc(v_value_1296_);
lean_inc(v_key_1295_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_key_1295_);
lean_ctor_set(v___x_1298_, 1, v_value_1296_);
v___x_1299_ = lean_array_push(v_x_1293_, v___x_1298_);
v_x_1293_ = v___x_1299_;
v_x_1294_ = v_tail_1297_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1301_, v_x_1302_);
lean_dec(v_x_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1304_, size_t v_i_1305_, size_t v_stop_1306_, lean_object* v_b_1307_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_eq(v_i_1305_, v_stop_1306_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; size_t v___x_1311_; size_t v___x_1312_; 
v___x_1309_ = lean_array_uget_borrowed(v_as_1304_, v_i_1305_);
v___x_1310_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1307_, v___x_1309_);
v___x_1311_ = ((size_t)1ULL);
v___x_1312_ = lean_usize_add(v_i_1305_, v___x_1311_);
v_i_1305_ = v___x_1312_;
v_b_1307_ = v___x_1310_;
goto _start;
}
else
{
return v_b_1307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1314_, lean_object* v_i_1315_, lean_object* v_stop_1316_, lean_object* v_b_1317_){
_start:
{
size_t v_i_boxed_1318_; size_t v_stop_boxed_1319_; lean_object* v_res_1320_; 
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_stop_boxed_1319_ = lean_unbox_usize(v_stop_1316_);
lean_dec(v_stop_1316_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1314_, v_i_boxed_1318_, v_stop_boxed_1319_, v_b_1317_);
lean_dec_ref(v_as_1314_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v_scopes_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_opts_1328_; lean_object* v___x_1329_; 
v___x_1324_ = lean_st_ref_get(v___y_1322_);
v_scopes_1325_ = lean_ctor_get(v___x_1324_, 2);
lean_inc(v_scopes_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1327_ = l_List_head_x21___redArg(v___x_1326_, v_scopes_1325_);
lean_dec(v_scopes_1325_);
v_opts_1328_ = lean_ctor_get(v___x_1327_, 1);
lean_inc_ref(v_opts_1328_);
lean_dec(v___x_1327_);
v___x_1329_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1328_, v___y_1322_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = lean_unsigned_to_nat(16u);
v___x_1336_ = lean_mk_array(v___x_1335_, v___x_1334_);
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___x_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1412_; 
v___x_1344_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1341_, v___y_1342_);
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1412_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1412_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1350_ = l_Lean_Linter_getLinterValue(v___x_1349_, v_a_1345_);
lean_dec(v_a_1345_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_box(0);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1353_ = v___x_1347_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
uint8_t v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = 0;
v___x_1356_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1340_, v___x_1355_);
if (lean_obj_tag(v___x_1356_) == 1)
{
lean_object* v_val_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_infoState_1362_; lean_object* v_trees_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; size_t v_sz_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
lean_del_object(v___x_1347_);
v_val_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_st_ref_get(v___y_1342_);
v___x_1359_ = lean_unsigned_to_nat(0u);
v___x_1360_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1361_ = lean_st_mk_ref(v___x_1360_);
v_infoState_1362_ = lean_ctor_get(v___x_1358_, 8);
lean_inc_ref(v_infoState_1362_);
lean_dec(v___x_1358_);
v_trees_1363_ = lean_ctor_get(v_infoState_1362_, 2);
lean_inc_ref(v_trees_1363_);
lean_dec_ref(v_infoState_1362_);
v___x_1364_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1363_);
lean_dec_ref(v_trees_1363_);
v___x_1365_ = lean_box(0);
v_sz_1366_ = lean_array_size(v___x_1364_);
v___x_1367_ = ((size_t)0ULL);
lean_inc(v___x_1361_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1350_, v___x_1361_, v_val_1357_, v___x_1364_, v_sz_1366_, v___x_1367_, v___x_1365_, v___y_1341_, v___y_1342_);
lean_dec_ref(v___x_1364_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; lean_object* v___y_1371_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1395_; lean_object* v_size_1401_; lean_object* v_buckets_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
lean_dec_ref_known(v___x_1368_, 1);
v___x_1369_ = lean_st_ref_get(v___x_1361_);
lean_dec(v___x_1361_);
v_size_1401_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_size_1401_);
v_buckets_1402_ = lean_ctor_get(v___x_1369_, 1);
lean_inc_ref(v_buckets_1402_);
lean_dec(v___x_1369_);
v___x_1403_ = lean_mk_empty_array_with_capacity(v_size_1401_);
lean_dec(v_size_1401_);
v___x_1404_ = lean_array_get_size(v_buckets_1402_);
v___x_1405_ = lean_nat_dec_lt(v___x_1359_, v___x_1404_);
if (v___x_1405_ == 0)
{
lean_dec_ref(v_buckets_1402_);
v___y_1395_ = v___x_1403_;
goto v___jp_1394_;
}
else
{
size_t v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_usize_of_nat(v___x_1404_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1402_, v___x_1367_, v___x_1406_, v___x_1403_);
lean_dec_ref(v_buckets_1402_);
v___y_1395_ = v___x_1407_;
goto v___jp_1394_;
}
v___jp_1370_:
{
size_t v_sz_1372_; lean_object* v___x_1373_; 
v_sz_1372_ = lean_array_size(v___y_1371_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1371_, v_sz_1372_, v___x_1367_, v___x_1365_, v___y_1341_, v___y_1342_);
lean_dec_ref(v___y_1371_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; 
v_unused_1381_ = lean_ctor_get(v___x_1373_, 0);
lean_dec(v_unused_1381_);
v___x_1375_ = v___x_1373_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_dec(v___x_1373_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1365_);
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1365_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
else
{
return v___x_1373_;
}
}
v___jp_1382_:
{
lean_object* v___x_1387_; 
v___x_1387_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1385_, v___y_1383_, v___y_1384_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
v___y_1371_ = v___x_1387_;
goto v___jp_1370_;
}
v___jp_1388_:
{
uint8_t v___x_1393_; 
v___x_1393_ = lean_nat_dec_le(v___y_1392_, v___y_1389_);
if (v___x_1393_ == 0)
{
lean_dec(v___y_1389_);
lean_inc(v___y_1392_);
v___y_1383_ = v___y_1390_;
v___y_1384_ = v___y_1392_;
v___y_1385_ = v___y_1391_;
v___y_1386_ = v___y_1392_;
goto v___jp_1382_;
}
else
{
v___y_1383_ = v___y_1390_;
v___y_1384_ = v___y_1392_;
v___y_1385_ = v___y_1391_;
v___y_1386_ = v___y_1389_;
goto v___jp_1382_;
}
}
v___jp_1394_:
{
lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1396_ = lean_array_get_size(v___y_1395_);
v___x_1397_ = lean_nat_dec_eq(v___x_1396_, v___x_1359_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1398_ = lean_unsigned_to_nat(1u);
v___x_1399_ = lean_nat_sub(v___x_1396_, v___x_1398_);
v___x_1400_ = lean_nat_dec_le(v___x_1359_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_inc(v___x_1399_);
v___y_1389_ = v___x_1399_;
v___y_1390_ = v___y_1395_;
v___y_1391_ = v___x_1396_;
v___y_1392_ = v___x_1399_;
goto v___jp_1388_;
}
else
{
v___y_1389_ = v___x_1399_;
v___y_1390_ = v___y_1395_;
v___y_1391_ = v___x_1396_;
v___y_1392_ = v___x_1359_;
goto v___jp_1388_;
}
}
else
{
v___y_1371_ = v___y_1395_;
goto v___jp_1370_;
}
}
}
else
{
lean_dec(v___x_1361_);
return v___x_1368_;
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec(v___x_1356_);
v___x_1408_ = lean_box(0);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1408_);
v___x_1410_ = v___x_1347_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v_cmdStx_1413_);
return v_res_1417_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_a_1429_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1428_, v_a_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_a_1433_){
_start:
{
uint8_t v_res_1434_; lean_object* v_r_1435_; 
v_res_1434_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1431_, v_m_1432_, v_a_1433_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_m_1432_);
v_r_1435_ = lean_box(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1436_, lean_object* v_m_1437_, lean_object* v_a_1438_, lean_object* v_b_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1437_, v_a_1438_, v_b_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1441_, lean_object* v_val_1442_, lean_object* v_info_1443_, lean_object* v___x_1444_, lean_object* v_val_1445_, uint8_t v___x_1446_, lean_object* v_as_1447_, lean_object* v_as_x27_1448_, lean_object* v_b_1449_, lean_object* v_a_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1441_, v_val_1442_, v_info_1443_, v___x_1444_, v_val_1445_, v___x_1446_, v_as_x27_1448_, v_b_1449_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1455_, lean_object* v_val_1456_, lean_object* v_info_1457_, lean_object* v___x_1458_, lean_object* v_val_1459_, lean_object* v___x_1460_, lean_object* v_as_1461_, lean_object* v_as_x27_1462_, lean_object* v_b_1463_, lean_object* v_a_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
uint8_t v___x_20142__boxed_1468_; lean_object* v_res_1469_; 
v___x_20142__boxed_1468_ = lean_unbox(v___x_1460_);
v_res_1469_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1455_, v_val_1456_, v_info_1457_, v___x_1458_, v_val_1459_, v___x_20142__boxed_1468_, v_as_1461_, v_as_x27_1462_, v_b_1463_, v_a_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v_as_x27_1462_);
lean_dec(v_as_1461_);
lean_dec_ref(v_info_1457_);
lean_dec(v_val_1456_);
lean_dec_ref(v_str_1455_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1470_, lean_object* v_as_1471_, lean_object* v_lo_1472_, lean_object* v_hi_1473_, lean_object* v_w_1474_, lean_object* v_hlo_1475_, lean_object* v_hhi_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1470_, v_as_1471_, v_lo_1472_, v_hi_1473_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1478_, lean_object* v_as_1479_, lean_object* v_lo_1480_, lean_object* v_hi_1481_, lean_object* v_w_1482_, lean_object* v_hlo_1483_, lean_object* v_hhi_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1478_, v_as_1479_, v_lo_1480_, v_hi_1481_, v_w_1482_, v_hlo_1483_, v_hhi_1484_);
lean_dec(v_hi_1481_);
lean_dec(v_n_1478_);
return v_res_1485_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1486_, lean_object* v_a_1487_, lean_object* v_x_1488_){
_start:
{
uint8_t v___x_1489_; 
v___x_1489_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1487_, v_x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1490_, lean_object* v_a_1491_, lean_object* v_x_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1490_, v_a_1491_, v_x_1492_);
lean_dec(v_x_1492_);
lean_dec_ref(v_a_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1495_, lean_object* v_data_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1498_, lean_object* v_a_1499_, lean_object* v_b_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1499_, v_b_1500_, v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1504_, v___y_1505_, v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_msg_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1509_, v_msg_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1515_, lean_object* v_preNode_1516_, lean_object* v_postNode_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1516_, v_postNode_1517_, v_x_1518_, v_x_1519_, v___y_1520_, v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_preNode_1525_, lean_object* v_postNode_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1524_, v_preNode_1525_, v_postNode_1526_, v_x_1527_, v_x_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object* v_n_1533_, lean_object* v_lo_1534_, lean_object* v_hi_1535_, lean_object* v_hhi_1536_, lean_object* v_pivot_1537_, lean_object* v_as_1538_, lean_object* v_i_1539_, lean_object* v_k_1540_, lean_object* v_ilo_1541_, lean_object* v_ik_1542_, lean_object* v_w_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1535_, v_pivot_1537_, v_as_1538_, v_i_1539_, v_k_1540_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object* v_n_1545_, lean_object* v_lo_1546_, lean_object* v_hi_1547_, lean_object* v_hhi_1548_, lean_object* v_pivot_1549_, lean_object* v_as_1550_, lean_object* v_i_1551_, lean_object* v_k_1552_, lean_object* v_ilo_1553_, lean_object* v_ik_1554_, lean_object* v_w_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_1545_, v_lo_1546_, v_hi_1547_, v_hhi_1548_, v_pivot_1549_, v_as_1550_, v_i_1551_, v_k_1552_, v_ilo_1553_, v_ik_1554_, v_w_1555_);
lean_dec_ref(v_pivot_1549_);
lean_dec(v_hi_1547_);
lean_dec(v_lo_1546_);
lean_dec(v_n_1545_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1557_, lean_object* v_i_1558_, lean_object* v_source_1559_, lean_object* v_target_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1558_, v_source_1559_, v_target_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1562_, lean_object* v_preNode_1563_, lean_object* v_postNode_1564_, lean_object* v___x_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1563_, v_postNode_1564_, v___x_1565_, v_x_1566_, v_x_1567_, v___y_1568_, v___y_1569_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1572_, lean_object* v_preNode_1573_, lean_object* v_postNode_1574_, lean_object* v___x_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1572_, v_preNode_1573_, v_postNode_1574_, v___x_1575_, v_x_1576_, v_x_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1582_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1593_, v_x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1598_ = l_Lean_Elab_Command_addLinter(v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1600_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_ConstructorAsVariable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
