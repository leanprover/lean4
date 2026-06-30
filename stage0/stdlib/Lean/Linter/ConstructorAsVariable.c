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
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_114_ = lean_st_ref_set(v___y_95_, v___x_113_);
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
lean_object* v___x_145_; lean_object* v_fst_146_; lean_object* v_fst_147_; lean_object* v_start_148_; lean_object* v_start_149_; uint8_t v___x_150_; 
v___x_145_ = lean_array_fget_borrowed(v_as_139_, v_k_141_);
v_fst_146_ = lean_ctor_get(v___x_145_, 0);
v_fst_147_ = lean_ctor_get(v_pivot_138_, 0);
v_start_148_ = lean_ctor_get(v_fst_146_, 0);
v_start_149_ = lean_ctor_get(v_fst_147_, 0);
v___x_150_ = lean_nat_dec_lt(v_start_148_, v_start_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = lean_nat_add(v_k_141_, v___x_151_);
lean_dec(v_k_141_);
v_k_141_ = v___x_152_;
goto _start;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = lean_array_fswap(v_as_139_, v_i_140_, v_k_141_);
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_nat_add(v_i_140_, v___x_155_);
lean_dec(v_i_140_);
v___x_157_ = lean_nat_add(v_k_141_, v___x_155_);
lean_dec(v_k_141_);
v_as_139_ = v___x_154_;
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
lean_object* v_fst_167_; lean_object* v_fst_168_; lean_object* v_start_169_; lean_object* v_start_170_; uint8_t v___x_171_; 
v_fst_167_ = lean_ctor_get(v_x1_165_, 0);
v_fst_168_ = lean_ctor_get(v_x2_166_, 0);
v_start_169_ = lean_ctor_get(v_fst_167_, 0);
v_start_170_ = lean_ctor_get(v_fst_168_, 0);
v___x_171_ = lean_nat_dec_lt(v_start_169_, v_start_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0___boxed(lean_object* v_x1_172_, lean_object* v_x2_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v_x1_172_, v_x2_173_);
lean_dec_ref(v_x2_173_);
lean_dec_ref(v_x1_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(lean_object* v_n_176_, lean_object* v_as_177_, lean_object* v_lo_178_, lean_object* v_hi_179_){
_start:
{
lean_object* v___y_181_; uint8_t v___x_191_; 
v___x_191_ = lean_nat_dec_lt(v_lo_178_, v_hi_179_);
if (v___x_191_ == 0)
{
lean_dec(v_lo_178_);
return v_as_177_;
}
else
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v_mid_194_; lean_object* v___y_196_; lean_object* v___y_202_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_192_ = lean_nat_add(v_lo_178_, v_hi_179_);
v___x_193_ = lean_unsigned_to_nat(1u);
v_mid_194_ = lean_nat_shiftr(v___x_192_, v___x_193_);
lean_dec(v___x_192_);
v___x_207_ = lean_array_fget_borrowed(v_as_177_, v_mid_194_);
v___x_208_ = lean_array_fget_borrowed(v_as_177_, v_lo_178_);
v___x_209_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
v___y_202_ = v_as_177_;
goto v___jp_201_;
}
else
{
lean_object* v___x_210_; 
v___x_210_ = lean_array_fswap(v_as_177_, v_lo_178_, v_mid_194_);
v___y_202_ = v___x_210_;
goto v___jp_201_;
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_197_ = lean_array_fget_borrowed(v___y_196_, v_mid_194_);
v___x_198_ = lean_array_fget_borrowed(v___y_196_, v_hi_179_);
v___x_199_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec(v_mid_194_);
v___y_181_ = v___y_196_;
goto v___jp_180_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = lean_array_fswap(v___y_196_, v_mid_194_, v_hi_179_);
lean_dec(v_mid_194_);
v___y_181_ = v___x_200_;
goto v___jp_180_;
}
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_203_ = lean_array_fget_borrowed(v___y_202_, v_hi_179_);
v___x_204_ = lean_array_fget_borrowed(v___y_202_, v_lo_178_);
v___x_205_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___lam__0(v___x_203_, v___x_204_);
if (v___x_205_ == 0)
{
v___y_196_ = v___y_202_;
goto v___jp_195_;
}
else
{
lean_object* v___x_206_; 
v___x_206_ = lean_array_fswap(v___y_202_, v_lo_178_, v_hi_179_);
v___y_196_ = v___x_206_;
goto v___jp_195_;
}
}
}
v___jp_180_:
{
lean_object* v_pivot_182_; lean_object* v___x_183_; lean_object* v_fst_184_; lean_object* v_snd_185_; uint8_t v___x_186_; 
v_pivot_182_ = lean_array_fget(v___y_181_, v_hi_179_);
lean_inc_n(v_lo_178_, 2);
v___x_183_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_179_, v_pivot_182_, v___y_181_, v_lo_178_, v_lo_178_);
lean_dec(v_pivot_182_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_fst_184_);
v_snd_185_ = lean_ctor_get(v___x_183_, 1);
lean_inc(v_snd_185_);
lean_dec_ref(v___x_183_);
v___x_186_ = lean_nat_dec_le(v_hi_179_, v_fst_184_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_187_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_176_, v_snd_185_, v_lo_178_, v_fst_184_);
v___x_188_ = lean_unsigned_to_nat(1u);
v___x_189_ = lean_nat_add(v_fst_184_, v___x_188_);
lean_dec(v_fst_184_);
v_as_177_ = v___x_187_;
v_lo_178_ = v___x_189_;
goto _start;
}
else
{
lean_dec(v_fst_184_);
lean_dec(v_lo_178_);
return v_snd_185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg___boxed(lean_object* v_n_211_, lean_object* v_as_212_, lean_object* v_lo_213_, lean_object* v_hi_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_211_, v_as_212_, v_lo_213_, v_hi_214_);
lean_dec(v_hi_214_);
lean_dec(v_n_211_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(uint8_t v___y_217_, uint8_t v_suppressElabErrors_218_, lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 1)
{
lean_object* v_pre_220_; 
v_pre_220_ = lean_ctor_get(v_x_219_, 0);
if (lean_obj_tag(v_pre_220_) == 0)
{
lean_object* v_str_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_str_221_ = lean_ctor_get(v_x_219_, 1);
v___x_222_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___closed__0));
v___x_223_ = lean_string_dec_eq(v_str_221_, v___x_222_);
if (v___x_223_ == 0)
{
return v___y_217_;
}
else
{
return v_suppressElabErrors_218_;
}
}
else
{
return v___y_217_;
}
}
else
{
return v___y_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed(lean_object* v___y_224_, lean_object* v_suppressElabErrors_225_, lean_object* v_x_226_){
_start:
{
uint8_t v___y_21710__boxed_227_; uint8_t v_suppressElabErrors_boxed_228_; uint8_t v_res_229_; lean_object* v_r_230_; 
v___y_21710__boxed_227_ = lean_unbox(v___y_224_);
v_suppressElabErrors_boxed_228_ = lean_unbox(v_suppressElabErrors_225_);
v_res_229_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21710__boxed_227_, v_suppressElabErrors_boxed_228_, v_x_226_);
lean_dec(v_x_226_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(lean_object* v_opts_231_, lean_object* v_opt_232_){
_start:
{
lean_object* v_name_233_; lean_object* v_defValue_234_; lean_object* v_map_235_; lean_object* v___x_236_; 
v_name_233_ = lean_ctor_get(v_opt_232_, 0);
v_defValue_234_ = lean_ctor_get(v_opt_232_, 1);
v_map_235_ = lean_ctor_get(v_opts_231_, 0);
v___x_236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_235_, v_name_233_);
if (lean_obj_tag(v___x_236_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = lean_unbox(v_defValue_234_);
return v___x_237_;
}
else
{
lean_object* v_val_238_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_236_, 1);
if (lean_obj_tag(v_val_238_) == 1)
{
uint8_t v_v_239_; 
v_v_239_ = lean_ctor_get_uint8(v_val_238_, 0);
lean_dec_ref_known(v_val_238_, 0);
return v_v_239_;
}
else
{
uint8_t v___x_240_; 
lean_dec(v_val_238_);
v___x_240_ = lean_unbox(v_defValue_234_);
return v___x_240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23___boxed(lean_object* v_opts_241_, lean_object* v_opt_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_241_, v_opt_242_);
lean_dec_ref(v_opt_242_);
lean_dec_ref(v_opts_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_245_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
lean_ctor_set(v___x_250_, 2, v___x_249_);
lean_ctor_set(v___x_250_, 3, v___x_249_);
lean_ctor_set(v___x_250_, 4, v___x_248_);
lean_ctor_set(v___x_250_, 5, v___x_248_);
lean_ctor_set(v___x_250_, 6, v___x_248_);
lean_ctor_set(v___x_250_, 7, v___x_248_);
lean_ctor_set(v___x_250_, 8, v___x_248_);
lean_ctor_set(v___x_250_, 9, v___x_248_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_unsigned_to_nat(32u);
v___x_252_ = lean_mk_empty_array_with_capacity(v___x_251_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4(void){
_start:
{
size_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_254_ = ((size_t)5ULL);
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = lean_unsigned_to_nat(32u);
v___x_257_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_258_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__3);
v___x_259_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
lean_ctor_set(v___x_259_, 2, v___x_255_);
lean_ctor_set(v___x_259_, 3, v___x_255_);
lean_ctor_set_usize(v___x_259_, 4, v___x_254_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_box(1);
v___x_261_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__4);
v___x_262_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__1);
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_260_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(lean_object* v_msgData_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; lean_object* v_env_268_; lean_object* v___x_269_; lean_object* v_scopes_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_opts_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_267_ = lean_st_ref_get(v___y_265_);
v_env_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_env_268_);
lean_dec(v___x_267_);
v___x_269_ = lean_st_ref_get(v___y_265_);
v_scopes_270_ = lean_ctor_get(v___x_269_, 2);
lean_inc(v_scopes_270_);
lean_dec(v___x_269_);
v___x_271_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_272_ = l_List_head_x21___redArg(v___x_271_, v_scopes_270_);
lean_dec(v_scopes_270_);
v_opts_273_ = lean_ctor_get(v___x_272_, 1);
lean_inc_ref(v_opts_273_);
lean_dec(v___x_272_);
v___x_274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__2);
v___x_275_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___closed__5);
v___x_276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_276_, 0, v_env_268_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_275_);
lean_ctor_set(v___x_276_, 3, v_opts_273_);
v___x_277_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_msgData_264_);
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg___boxed(lean_object* v_msgData_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_279_, v___y_280_);
lean_dec(v___y_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(lean_object* v_ref_284_, lean_object* v_msgData_285_, uint8_t v_severity_286_, uint8_t v_isSilent_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___y_292_; lean_object* v___y_293_; uint8_t v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; uint8_t v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; uint8_t v___y_355_; uint8_t v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; lean_object* v___y_359_; uint8_t v___y_383_; lean_object* v___y_384_; uint8_t v___y_385_; uint8_t v___y_386_; lean_object* v___y_387_; uint8_t v___y_391_; uint8_t v___y_392_; uint8_t v___y_393_; uint8_t v___x_408_; uint8_t v___y_410_; uint8_t v___y_411_; uint8_t v___y_412_; uint8_t v___y_414_; uint8_t v___x_426_; 
v___x_408_ = 2;
v___x_426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_286_, v___x_408_);
if (v___x_426_ == 0)
{
v___y_414_ = v___x_426_;
goto v___jp_413_;
}
else
{
uint8_t v___x_427_; 
lean_inc_ref(v_msgData_285_);
v___x_427_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_285_);
v___y_414_ = v___x_427_;
goto v___jp_413_;
}
v___jp_291_:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Elab_Command_getScope___redArg(v___y_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_302_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_300_, 1);
v___x_302_ = l_Lean_Elab_Command_getScope___redArg(v___y_299_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_337_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_337_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_337_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_337_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v_currNamespace_308_; lean_object* v_openDecls_309_; lean_object* v_env_310_; lean_object* v_messages_311_; lean_object* v_scopes_312_; lean_object* v_usedQuotCtxts_313_; lean_object* v_nextMacroScope_314_; lean_object* v_maxRecDepth_315_; lean_object* v_ngen_316_; lean_object* v_auxDeclNGen_317_; lean_object* v_infoState_318_; lean_object* v_traceState_319_; lean_object* v_snapshotTasks_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_336_; 
v___x_307_ = lean_st_ref_take(v___y_299_);
v_currNamespace_308_ = lean_ctor_get(v_a_301_, 2);
lean_inc(v_currNamespace_308_);
lean_dec(v_a_301_);
v_openDecls_309_ = lean_ctor_get(v_a_303_, 3);
lean_inc(v_openDecls_309_);
lean_dec(v_a_303_);
v_env_310_ = lean_ctor_get(v___x_307_, 0);
v_messages_311_ = lean_ctor_get(v___x_307_, 1);
v_scopes_312_ = lean_ctor_get(v___x_307_, 2);
v_usedQuotCtxts_313_ = lean_ctor_get(v___x_307_, 3);
v_nextMacroScope_314_ = lean_ctor_get(v___x_307_, 4);
v_maxRecDepth_315_ = lean_ctor_get(v___x_307_, 5);
v_ngen_316_ = lean_ctor_get(v___x_307_, 6);
v_auxDeclNGen_317_ = lean_ctor_get(v___x_307_, 7);
v_infoState_318_ = lean_ctor_get(v___x_307_, 8);
v_traceState_319_ = lean_ctor_get(v___x_307_, 9);
v_snapshotTasks_320_ = lean_ctor_get(v___x_307_, 10);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_336_ == 0)
{
v___x_322_ = v___x_307_;
v_isShared_323_ = v_isSharedCheck_336_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_snapshotTasks_320_);
lean_inc(v_traceState_319_);
lean_inc(v_infoState_318_);
lean_inc(v_auxDeclNGen_317_);
lean_inc(v_ngen_316_);
lean_inc(v_maxRecDepth_315_);
lean_inc(v_nextMacroScope_314_);
lean_inc(v_usedQuotCtxts_313_);
lean_inc(v_scopes_312_);
lean_inc(v_messages_311_);
lean_inc(v_env_310_);
lean_dec(v___x_307_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_336_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v_currNamespace_308_);
lean_ctor_set(v___x_324_, 1, v_openDecls_309_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___y_293_);
lean_inc_ref(v___y_298_);
lean_inc_ref(v___y_296_);
v___x_326_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_326_, 0, v___y_296_);
lean_ctor_set(v___x_326_, 1, v___y_295_);
lean_ctor_set(v___x_326_, 2, v___y_292_);
lean_ctor_set(v___x_326_, 3, v___y_298_);
lean_ctor_set(v___x_326_, 4, v___x_325_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*5, v___y_297_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*5 + 1, v___y_294_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*5 + 2, v_isSilent_287_);
v___x_327_ = l_Lean_MessageLog_add(v___x_326_, v_messages_311_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 1, v___x_327_);
v___x_329_ = v___x_322_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_env_310_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_335_, 2, v_scopes_312_);
lean_ctor_set(v_reuseFailAlloc_335_, 3, v_usedQuotCtxts_313_);
lean_ctor_set(v_reuseFailAlloc_335_, 4, v_nextMacroScope_314_);
lean_ctor_set(v_reuseFailAlloc_335_, 5, v_maxRecDepth_315_);
lean_ctor_set(v_reuseFailAlloc_335_, 6, v_ngen_316_);
lean_ctor_set(v_reuseFailAlloc_335_, 7, v_auxDeclNGen_317_);
lean_ctor_set(v_reuseFailAlloc_335_, 8, v_infoState_318_);
lean_ctor_set(v_reuseFailAlloc_335_, 9, v_traceState_319_);
lean_ctor_set(v_reuseFailAlloc_335_, 10, v_snapshotTasks_320_);
v___x_329_ = v_reuseFailAlloc_335_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = lean_st_ref_set(v___y_299_, v___x_329_);
v___x_331_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_331_);
v___x_333_ = v___x_305_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_a_301_);
lean_dec_ref(v___y_295_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
v_a_338_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_302_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_302_);
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
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___y_295_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
v_a_346_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_300_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_300_);
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
v___jp_354_:
{
lean_object* v_fileName_360_; lean_object* v_fileMap_361_; uint8_t v_suppressElabErrors_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_381_; 
v_fileName_360_ = lean_ctor_get(v___y_288_, 0);
v_fileMap_361_ = lean_ctor_get(v___y_288_, 1);
v_suppressElabErrors_362_ = lean_ctor_get_uint8(v___y_288_, sizeof(void*)*10);
v___x_363_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_285_);
v___x_364_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_363_, v___y_289_);
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
lean_inc_ref_n(v_fileMap_361_, 2);
v___x_369_ = l_Lean_FileMap_toPosition(v_fileMap_361_, v___y_357_);
lean_dec(v___y_357_);
v___x_370_ = l_Lean_FileMap_toPosition(v_fileMap_361_, v___y_359_);
lean_dec(v___y_359_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
v___x_372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_362_ == 0)
{
lean_del_object(v___x_367_);
v___y_292_ = v___x_371_;
v___y_293_ = v_a_365_;
v___y_294_ = v___y_356_;
v___y_295_ = v___x_369_;
v___y_296_ = v_fileName_360_;
v___y_297_ = v___y_358_;
v___y_298_ = v___x_372_;
v___y_299_ = v___y_289_;
goto v___jp_291_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___f_375_; uint8_t v___x_376_; 
v___x_373_ = lean_box(v___y_355_);
v___x_374_ = lean_box(v_suppressElabErrors_362_);
v___f_375_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed), 3, 2);
lean_closure_set(v___f_375_, 0, v___x_373_);
lean_closure_set(v___f_375_, 1, v___x_374_);
lean_inc(v_a_365_);
v___x_376_ = l_Lean_MessageData_hasTag(v___f_375_, v_a_365_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_dec_ref_known(v___x_371_, 1);
lean_dec_ref(v___x_369_);
lean_dec(v_a_365_);
v___x_377_ = lean_box(0);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_377_);
v___x_379_ = v___x_367_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
else
{
lean_del_object(v___x_367_);
v___y_292_ = v___x_371_;
v___y_293_ = v_a_365_;
v___y_294_ = v___y_356_;
v___y_295_ = v___x_369_;
v___y_296_ = v_fileName_360_;
v___y_297_ = v___y_358_;
v___y_298_ = v___x_372_;
v___y_299_ = v___y_289_;
goto v___jp_291_;
}
}
}
}
v___jp_382_:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Syntax_getTailPos_x3f(v___y_384_, v___y_386_);
lean_dec(v___y_384_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_inc(v___y_387_);
v___y_355_ = v___y_383_;
v___y_356_ = v___y_385_;
v___y_357_ = v___y_387_;
v___y_358_ = v___y_386_;
v___y_359_ = v___y_387_;
goto v___jp_354_;
}
else
{
lean_object* v_val_389_; 
v_val_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_val_389_);
lean_dec_ref_known(v___x_388_, 1);
v___y_355_ = v___y_383_;
v___y_356_ = v___y_385_;
v___y_357_ = v___y_387_;
v___y_358_ = v___y_386_;
v___y_359_ = v_val_389_;
goto v___jp_354_;
}
}
v___jp_390_:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Elab_Command_getRef___redArg(v___y_288_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v_ref_396_; lean_object* v___x_397_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v_ref_396_ = l_Lean_replaceRef(v_ref_284_, v_a_395_);
lean_dec(v_a_395_);
v___x_397_ = l_Lean_Syntax_getPos_x3f(v_ref_396_, v___y_392_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_unsigned_to_nat(0u);
v___y_383_ = v___y_391_;
v___y_384_ = v_ref_396_;
v___y_385_ = v___y_393_;
v___y_386_ = v___y_392_;
v___y_387_ = v___x_398_;
goto v___jp_382_;
}
else
{
lean_object* v_val_399_; 
v_val_399_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v___x_397_, 1);
v___y_383_ = v___y_391_;
v___y_384_ = v_ref_396_;
v___y_385_ = v___y_393_;
v___y_386_ = v___y_392_;
v___y_387_ = v_val_399_;
goto v___jp_382_;
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v_msgData_285_);
v_a_400_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_394_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_394_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
v___jp_409_:
{
if (v___y_412_ == 0)
{
v___y_391_ = v___y_410_;
v___y_392_ = v___y_411_;
v___y_393_ = v_severity_286_;
goto v___jp_390_;
}
else
{
v___y_391_ = v___y_410_;
v___y_392_ = v___y_411_;
v___y_393_ = v___x_408_;
goto v___jp_390_;
}
}
v___jp_413_:
{
if (v___y_414_ == 0)
{
lean_object* v___x_415_; lean_object* v_scopes_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_opts_419_; uint8_t v___x_420_; uint8_t v___x_421_; 
v___x_415_ = lean_st_ref_get(v___y_289_);
v_scopes_416_ = lean_ctor_get(v___x_415_, 2);
lean_inc(v_scopes_416_);
lean_dec(v___x_415_);
v___x_417_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_418_ = l_List_head_x21___redArg(v___x_417_, v_scopes_416_);
lean_dec(v_scopes_416_);
v_opts_419_ = lean_ctor_get(v___x_418_, 1);
lean_inc_ref(v_opts_419_);
lean_dec(v___x_418_);
v___x_420_ = 1;
v___x_421_ = l_Lean_instBEqMessageSeverity_beq(v_severity_286_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec_ref(v_opts_419_);
v___y_410_ = v___y_414_;
v___y_411_ = v___y_414_;
v___y_412_ = v___x_421_;
goto v___jp_409_;
}
else
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = l_Lean_warningAsError;
v___x_423_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_419_, v___x_422_);
lean_dec_ref(v_opts_419_);
v___y_410_ = v___y_414_;
v___y_411_ = v___y_414_;
v___y_412_ = v___x_423_;
goto v___jp_409_;
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v_msgData_285_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object* v_ref_428_, lean_object* v_msgData_429_, lean_object* v_severity_430_, lean_object* v_isSilent_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
uint8_t v_severity_boxed_435_; uint8_t v_isSilent_boxed_436_; lean_object* v_res_437_; 
v_severity_boxed_435_ = lean_unbox(v_severity_430_);
v_isSilent_boxed_436_ = lean_unbox(v_isSilent_431_);
v_res_437_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_428_, v_msgData_429_, v_severity_boxed_435_, v_isSilent_boxed_436_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v_ref_428_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object* v_ref_438_, lean_object* v_msgData_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
uint8_t v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; 
v___x_443_ = 1;
v___x_444_ = 0;
v___x_445_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_438_, v_msgData_439_, v___x_443_, v___x_444_, v___y_440_, v___y_441_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object* v_ref_446_, lean_object* v_msgData_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_446_, v_msgData_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v_ref_446_);
return v_res_451_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* v_linterOption_458_, lean_object* v_stx_459_, lean_object* v_msg_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_name_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_482_; 
v_name_464_ = lean_ctor_get(v_linterOption_458_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v_linterOption_458_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v_linterOption_458_, 1);
lean_dec(v_unused_483_);
v___x_466_ = v_linterOption_458_;
v_isShared_467_ = v_isSharedCheck_482_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_name_464_);
lean_dec(v_linterOption_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_482_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_468_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
lean_inc(v_name_464_);
v___x_469_ = l_Lean_MessageData_ofName(v_name_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 7);
lean_ctor_set(v___x_466_, 1, v___x_469_);
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_471_ = v___x_466_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_481_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_disable_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_472_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v_disable_474_ = l_Lean_MessageData_note(v___x_473_);
v___x_475_ = l_Lean_Linter_linterMessageTag;
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v_msg_460_);
lean_ctor_set(v___x_476_, 1, v_disable_474_);
v___x_477_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_478_, 0, v_name_464_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
lean_inc(v_stx_459_);
v___x_479_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_479_, 0, v_stx_459_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_459_, v___x_479_, v___y_461_, v___y_462_);
lean_dec(v_stx_459_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_484_, lean_object* v_stx_485_, lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_484_, v_stx_485_, v_msg_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_490_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_508_ = l_Lean_stringToMessageData(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_509_, size_t v_sz_510_, size_t v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_b_512_);
return v___x_517_;
}
else
{
lean_object* v_a_518_; lean_object* v_snd_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_564_; 
v_a_518_ = lean_array_uget(v_as_509_, v_i_511_);
v_snd_519_ = lean_ctor_get(v_a_518_, 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_518_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v_a_518_, 0);
lean_dec(v_unused_565_);
v___x_521_ = v_a_518_;
v_isShared_522_ = v_isSharedCheck_564_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_snd_519_);
lean_dec(v_a_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_564_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_snd_523_; lean_object* v_fst_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_563_; 
v_snd_523_ = lean_ctor_get(v_snd_519_, 1);
v_fst_524_ = lean_ctor_get(v_snd_519_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_snd_519_);
if (v_isSharedCheck_563_ == 0)
{
v___x_526_ = v_snd_519_;
v_isShared_527_ = v_isSharedCheck_563_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_snd_523_);
lean_inc(v_fst_524_);
lean_dec(v_snd_519_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_563_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v_fst_528_; lean_object* v_snd_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_562_; 
v_fst_528_ = lean_ctor_get(v_snd_523_, 0);
v_snd_529_ = lean_ctor_get(v_snd_523_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_snd_523_);
if (v_isSharedCheck_562_ == 0)
{
v___x_531_ = v_snd_523_;
v_isShared_532_ = v_isSharedCheck_562_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snd_529_);
lean_inc(v_fst_528_);
lean_dec(v_snd_523_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_562_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_533_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_535_ = l_Lean_MessageData_ofName(v_fst_528_);
lean_inc_ref(v___x_535_);
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 7);
lean_ctor_set(v___x_531_, 1, v___x_535_);
lean_ctor_set(v___x_531_, 0, v___x_534_);
v___x_537_ = v___x_531_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_561_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_527_ == 0)
{
lean_ctor_set_tag(v___x_526_, 7);
lean_ctor_set(v___x_526_, 1, v___x_538_);
lean_ctor_set(v___x_526_, 0, v___x_537_);
v___x_540_ = v___x_526_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_537_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_560_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = l_Lean_MessageData_ofName(v_snd_529_);
lean_inc_ref(v___x_541_);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 7);
lean_ctor_set(v___x_521_, 1, v___x_541_);
lean_ctor_set(v___x_521_, 0, v___x_540_);
v___x_543_ = v___x_521_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_541_);
v___x_543_ = v_reuseFailAlloc_559_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_544_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_535_);
v___x_548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_541_);
v___x_551_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_550_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_545_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_533_, v_fst_524_, v___x_553_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; size_t v___x_556_; size_t v___x_557_; 
lean_dec_ref_known(v___x_554_, 1);
v___x_555_ = lean_box(0);
v___x_556_ = ((size_t)1ULL);
v___x_557_ = lean_usize_add(v_i_511_, v___x_556_);
v_i_511_ = v___x_557_;
v_b_512_ = v___x_555_;
goto _start;
}
else
{
return v___x_554_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
size_t v_sz_boxed_573_; size_t v_i_boxed_574_; lean_object* v_res_575_; 
v_sz_boxed_573_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_574_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_566_, v_sz_boxed_573_, v_i_boxed_574_, v_b_569_, v___y_570_, v___y_571_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v_as_566_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_box(v___x_576_);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___x_22328__boxed_592_; lean_object* v_res_593_; 
v___x_22328__boxed_592_ = lean_unbox(v___x_585_);
v_res_593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22328__boxed_592_, v_x_586_, v_x_587_, v_x_588_, v___y_589_, v___y_590_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec_ref(v_x_588_);
lean_dec_ref(v_x_587_);
lean_dec_ref(v_x_586_);
return v_res_593_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
uint8_t v___x_596_; 
v___x_596_ = 0;
return v___x_596_;
}
else
{
lean_object* v_key_597_; lean_object* v_tail_598_; uint8_t v___x_599_; 
v_key_597_ = lean_ctor_get(v_x_595_, 0);
v_tail_598_ = lean_ctor_get(v_x_595_, 2);
v___x_599_ = l_Lean_Syntax_instBEqRange_beq(v_key_597_, v_a_594_);
if (v___x_599_ == 0)
{
v_x_595_ = v_tail_598_;
goto _start;
}
else
{
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_601_, lean_object* v_x_602_){
_start:
{
uint8_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_601_, v_x_602_);
lean_dec(v_x_602_);
lean_dec_ref(v_a_601_);
v_r_604_ = lean_box(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_buckets_607_; lean_object* v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v_fold_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_buckets_607_ = lean_ctor_get(v_m_605_, 1);
v___x_608_ = lean_array_get_size(v_buckets_607_);
v___x_609_ = l_Lean_Syntax_instHashableRange_hash(v_a_606_);
v___x_610_ = 32ULL;
v___x_611_ = lean_uint64_shift_right(v___x_609_, v___x_610_);
v_fold_612_ = lean_uint64_xor(v___x_609_, v___x_611_);
v___x_613_ = 16ULL;
v___x_614_ = lean_uint64_shift_right(v_fold_612_, v___x_613_);
v___x_615_ = lean_uint64_xor(v_fold_612_, v___x_614_);
v___x_616_ = lean_uint64_to_usize(v___x_615_);
v___x_617_ = lean_usize_of_nat(v___x_608_);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v___x_617_, v___x_618_);
v___x_620_ = lean_usize_land(v___x_616_, v___x_619_);
v___x_621_ = lean_array_uget_borrowed(v_buckets_607_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_606_, v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_623_, lean_object* v_a_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_623_, v_a_624_);
lean_dec_ref(v_a_624_);
lean_dec_ref(v_m_623_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_627_, lean_object* v_b_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_dec(v_b_628_);
lean_dec_ref(v_a_627_);
return v_x_629_;
}
else
{
lean_object* v_key_630_; lean_object* v_value_631_; lean_object* v_tail_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_644_; 
v_key_630_ = lean_ctor_get(v_x_629_, 0);
v_value_631_ = lean_ctor_get(v_x_629_, 1);
v_tail_632_ = lean_ctor_get(v_x_629_, 2);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_629_);
if (v_isSharedCheck_644_ == 0)
{
v___x_634_ = v_x_629_;
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_tail_632_);
lean_inc(v_value_631_);
lean_inc(v_key_630_);
lean_dec(v_x_629_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_644_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___x_636_; 
v___x_636_ = l_Lean_Syntax_instBEqRange_beq(v_key_630_, v_a_627_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_627_, v_b_628_, v_tail_632_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 2, v___x_637_);
v___x_639_ = v___x_634_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_key_630_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_value_631_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
else
{
lean_object* v___x_642_; 
lean_dec(v_value_631_);
lean_dec(v_key_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 1, v_b_628_);
lean_ctor_set(v___x_634_, 0, v_a_627_);
v___x_642_ = v___x_634_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_627_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_b_628_);
lean_ctor_set(v_reuseFailAlloc_643_, 2, v_tail_632_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
return v_x_645_;
}
else
{
lean_object* v_key_647_; lean_object* v_value_648_; lean_object* v_tail_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_672_; 
v_key_647_ = lean_ctor_get(v_x_646_, 0);
v_value_648_ = lean_ctor_get(v_x_646_, 1);
v_tail_649_ = lean_ctor_get(v_x_646_, 2);
v_isSharedCheck_672_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_672_ == 0)
{
v___x_651_ = v_x_646_;
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_tail_649_);
lean_inc(v_value_648_);
lean_inc(v_key_647_);
lean_dec(v_x_646_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_672_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v_fold_657_; uint64_t v___x_658_; uint64_t v___x_659_; uint64_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_653_ = lean_array_get_size(v_x_645_);
v___x_654_ = l_Lean_Syntax_instHashableRange_hash(v_key_647_);
v___x_655_ = 32ULL;
v___x_656_ = lean_uint64_shift_right(v___x_654_, v___x_655_);
v_fold_657_ = lean_uint64_xor(v___x_654_, v___x_656_);
v___x_658_ = 16ULL;
v___x_659_ = lean_uint64_shift_right(v_fold_657_, v___x_658_);
v___x_660_ = lean_uint64_xor(v_fold_657_, v___x_659_);
v___x_661_ = lean_uint64_to_usize(v___x_660_);
v___x_662_ = lean_usize_of_nat(v___x_653_);
v___x_663_ = ((size_t)1ULL);
v___x_664_ = lean_usize_sub(v___x_662_, v___x_663_);
v___x_665_ = lean_usize_land(v___x_661_, v___x_664_);
v___x_666_ = lean_array_uget_borrowed(v_x_645_, v___x_665_);
lean_inc(v___x_666_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 2, v___x_666_);
v___x_668_ = v___x_651_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_key_647_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_value_648_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v___x_666_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; 
v___x_669_ = lean_array_uset(v_x_645_, v___x_665_, v___x_668_);
v_x_645_ = v___x_669_;
v_x_646_ = v_tail_649_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_673_, lean_object* v_source_674_, lean_object* v_target_675_){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_676_ = lean_array_get_size(v_source_674_);
v___x_677_ = lean_nat_dec_lt(v_i_673_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v_source_674_);
lean_dec(v_i_673_);
return v_target_675_;
}
else
{
lean_object* v_es_678_; lean_object* v___x_679_; lean_object* v_source_680_; lean_object* v_target_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_es_678_ = lean_array_fget(v_source_674_, v_i_673_);
v___x_679_ = lean_box(0);
v_source_680_ = lean_array_fset(v_source_674_, v_i_673_, v___x_679_);
v_target_681_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_675_, v_es_678_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_add(v_i_673_, v___x_682_);
lean_dec(v_i_673_);
v_i_673_ = v___x_683_;
v_source_674_ = v_source_680_;
v_target_675_ = v_target_681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_nbuckets_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_686_ = lean_array_get_size(v_data_685_);
v___x_687_ = lean_unsigned_to_nat(2u);
v_nbuckets_688_ = lean_nat_mul(v___x_686_, v___x_687_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_box(0);
v___x_691_ = lean_mk_array(v_nbuckets_688_, v___x_690_);
v___x_692_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_689_, v_data_685_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_693_, lean_object* v_a_694_, lean_object* v_b_695_){
_start:
{
lean_object* v_size_696_; lean_object* v_buckets_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_740_; 
v_size_696_ = lean_ctor_get(v_m_693_, 0);
v_buckets_697_ = lean_ctor_get(v_m_693_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_m_693_);
if (v_isSharedCheck_740_ == 0)
{
v___x_699_ = v_m_693_;
v_isShared_700_ = v_isSharedCheck_740_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_buckets_697_);
lean_inc(v_size_696_);
lean_dec(v_m_693_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_740_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v_fold_705_; uint64_t v___x_706_; uint64_t v___x_707_; uint64_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v_bkt_714_; uint8_t v___x_715_; 
v___x_701_ = lean_array_get_size(v_buckets_697_);
v___x_702_ = l_Lean_Syntax_instHashableRange_hash(v_a_694_);
v___x_703_ = 32ULL;
v___x_704_ = lean_uint64_shift_right(v___x_702_, v___x_703_);
v_fold_705_ = lean_uint64_xor(v___x_702_, v___x_704_);
v___x_706_ = 16ULL;
v___x_707_ = lean_uint64_shift_right(v_fold_705_, v___x_706_);
v___x_708_ = lean_uint64_xor(v_fold_705_, v___x_707_);
v___x_709_ = lean_uint64_to_usize(v___x_708_);
v___x_710_ = lean_usize_of_nat(v___x_701_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_sub(v___x_710_, v___x_711_);
v___x_713_ = lean_usize_land(v___x_709_, v___x_712_);
v_bkt_714_ = lean_array_uget_borrowed(v_buckets_697_, v___x_713_);
v___x_715_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_694_, v_bkt_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v_size_x27_717_; lean_object* v___x_718_; lean_object* v_buckets_x27_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_716_ = lean_unsigned_to_nat(1u);
v_size_x27_717_ = lean_nat_add(v_size_696_, v___x_716_);
lean_dec(v_size_696_);
lean_inc(v_bkt_714_);
v___x_718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_718_, 0, v_a_694_);
lean_ctor_set(v___x_718_, 1, v_b_695_);
lean_ctor_set(v___x_718_, 2, v_bkt_714_);
v_buckets_x27_719_ = lean_array_uset(v_buckets_697_, v___x_713_, v___x_718_);
v___x_720_ = lean_unsigned_to_nat(4u);
v___x_721_ = lean_nat_mul(v_size_x27_717_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(3u);
v___x_723_ = lean_nat_div(v___x_721_, v___x_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_array_get_size(v_buckets_x27_719_);
v___x_725_ = lean_nat_dec_le(v___x_723_, v___x_724_);
lean_dec(v___x_723_);
if (v___x_725_ == 0)
{
lean_object* v_val_726_; lean_object* v___x_728_; 
v_val_726_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_719_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_val_726_);
lean_ctor_set(v___x_699_, 0, v_size_x27_717_);
v___x_728_ = v___x_699_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_size_x27_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_val_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v___x_731_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v_buckets_x27_719_);
lean_ctor_set(v___x_699_, 0, v_size_x27_717_);
v___x_731_ = v___x_699_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_size_x27_717_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_buckets_x27_719_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v___x_733_; lean_object* v_buckets_x27_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
lean_inc(v_bkt_714_);
v___x_733_ = lean_box(0);
v_buckets_x27_734_ = lean_array_uset(v_buckets_697_, v___x_713_, v___x_733_);
v___x_735_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_694_, v_b_695_, v_bkt_714_);
v___x_736_ = lean_array_uset(v_buckets_x27_734_, v___x_713_, v___x_735_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 1, v___x_736_);
v___x_738_ = v___x_699_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_696_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_741_, lean_object* v_val_742_, lean_object* v_info_743_, lean_object* v___x_744_, lean_object* v_val_745_, uint8_t v___x_746_, lean_object* v_as_x27_747_, lean_object* v_b_748_, lean_object* v___y_749_){
_start:
{
if (lean_obj_tag(v_as_x27_747_) == 0)
{
lean_object* v___x_751_; 
lean_dec_ref(v_val_745_);
lean_dec(v___x_744_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v_b_748_);
return v___x_751_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v___x_754_; lean_object* v_env_755_; lean_object* v___x_756_; lean_object* v___x_769_; 
v_head_752_ = lean_ctor_get(v_as_x27_747_, 0);
v_tail_753_ = lean_ctor_get(v_as_x27_747_, 1);
v___x_754_ = lean_st_ref_get(v___y_749_);
v_env_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_ref(v_env_755_);
lean_dec(v___x_754_);
v___x_756_ = lean_box(0);
lean_inc(v_head_752_);
v___x_769_ = l_Lean_Environment_find_x3f(v_env_755_, v_head_752_, v___x_746_);
if (lean_obj_tag(v___x_769_) == 1)
{
lean_object* v_val_770_; 
v_val_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_769_, 1);
if (lean_obj_tag(v_val_770_) == 6)
{
lean_object* v_val_771_; lean_object* v_numFields_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_val_771_ = lean_ctor_get(v_val_770_, 0);
lean_inc_ref(v_val_771_);
lean_dec_ref_known(v_val_770_, 1);
v_numFields_772_ = lean_ctor_get(v_val_771_, 4);
lean_inc(v_numFields_772_);
lean_dec_ref(v_val_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_lt(v___x_773_, v_numFields_772_);
lean_dec(v_numFields_772_);
if (v___x_774_ == 0)
{
goto v___jp_757_;
}
else
{
v_as_x27_747_ = v_tail_753_;
v_b_748_ = v___x_756_;
goto _start;
}
}
else
{
lean_dec(v_val_770_);
goto v___jp_757_;
}
}
else
{
lean_dec(v___x_769_);
goto v___jp_757_;
}
v___jp_757_:
{
if (lean_obj_tag(v_head_752_) == 1)
{
lean_object* v_str_758_; uint8_t v___x_759_; 
v_str_758_ = lean_ctor_get(v_head_752_, 1);
v___x_759_ = lean_string_dec_eq(v_str_758_, v_str_741_);
if (v___x_759_ == 0)
{
v_as_x27_747_ = v_tail_753_;
v_b_748_ = v___x_756_;
goto _start;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_761_ = lean_st_ref_take(v_val_742_);
v___x_762_ = l_Lean_Elab_Info_stx(v_info_743_);
lean_inc_ref(v_head_752_);
lean_inc(v___x_744_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_744_);
lean_ctor_set(v___x_763_, 1, v_head_752_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
lean_inc_ref(v_val_745_);
v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_761_, v_val_745_, v___x_764_);
v___x_766_ = lean_st_ref_set(v_val_742_, v___x_765_);
v_as_x27_747_ = v_tail_753_;
v_b_748_ = v___x_756_;
goto _start;
}
}
else
{
v_as_x27_747_ = v_tail_753_;
v_b_748_ = v___x_756_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_776_, lean_object* v_val_777_, lean_object* v_info_778_, lean_object* v___x_779_, lean_object* v_val_780_, lean_object* v___x_781_, lean_object* v_as_x27_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v___x_22592__boxed_786_; lean_object* v_res_787_; 
v___x_22592__boxed_786_ = lean_unbox(v___x_781_);
v_res_787_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_776_, v_val_777_, v_info_778_, v___x_779_, v_val_780_, v___x_22592__boxed_786_, v_as_x27_782_, v_b_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec(v_as_x27_782_);
lean_dec_ref(v_info_778_);
lean_dec(v_val_777_);
lean_dec_ref(v_str_776_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_788_, v___y_790_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_794_, 1);
v___x_796_ = lean_whnf(v_a_795_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_796_;
}
else
{
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_804_, lean_object* v___x_805_, lean_object* v_val_806_, lean_object* v___x_807_, lean_object* v_ci_808_, lean_object* v_info_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
if (lean_obj_tag(v_info_809_) == 1)
{
lean_object* v_i_814_; lean_object* v_expr_815_; 
v_i_814_ = lean_ctor_get(v_info_809_, 0);
v_expr_815_ = lean_ctor_get(v_i_814_, 3);
if (lean_obj_tag(v_expr_815_) == 1)
{
lean_object* v_lctx_816_; lean_object* v_expectedType_x3f_817_; uint8_t v_isBinder_818_; lean_object* v_fvarId_819_; lean_object* v___x_820_; 
v_lctx_816_ = lean_ctor_get(v_i_814_, 1);
v_expectedType_x3f_817_ = lean_ctor_get(v_i_814_, 2);
v_isBinder_818_ = lean_ctor_get_uint8(v_i_814_, sizeof(void*)*4);
v_fvarId_819_ = lean_ctor_get(v_expr_815_, 0);
v___x_820_ = l_Lean_Elab_Info_range_x3f(v_info_809_);
if (lean_obj_tag(v___x_820_) == 1)
{
lean_object* v_val_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_976_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_976_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_976_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_val_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_976_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_825_ = lean_st_ref_get(v_val_804_);
v___x_826_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_825_, v_val_821_);
lean_dec(v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = l_Lean_Elab_Info_stx(v_info_809_);
v___x_828_ = l_Lean_Syntax_getHeadInfo(v___x_827_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_dec_ref_known(v___x_828_, 4);
if (v_isBinder_818_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v___x_827_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_805_);
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_805_);
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
lean_object* v___x_832_; 
lean_inc(v_fvarId_819_);
lean_inc_ref(v_lctx_816_);
v___x_832_ = lean_local_ctx_find(v_lctx_816_, v_fvarId_819_);
if (lean_obj_tag(v___x_832_) == 1)
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_966_; 
v_val_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_966_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_966_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_966_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_start_837_; uint8_t v___x_838_; 
v_start_837_ = lean_ctor_get(v_val_821_, 0);
v___x_838_ = l_Lean_Syntax_Range_contains(v_val_806_, v_start_837_, v___x_826_);
if (v___x_838_ == 0)
{
lean_object* v___x_840_; 
lean_dec(v_val_833_);
lean_dec(v___x_827_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
lean_ctor_set(v___x_835_, 0, v___x_805_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_805_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
else
{
if (v___x_826_ == 0)
{
lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_842_ = l_Lean_LocalDecl_userName(v_val_833_);
lean_dec(v_val_833_);
v___x_843_ = l_Lean_Name_hasMacroScopes(v___x_842_);
lean_dec(v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v_toCommandContextInfo_844_; lean_object* v_options_845_; lean_object* v___x_846_; 
v_toCommandContextInfo_844_ = lean_ctor_get(v_ci_808_, 0);
v_options_845_ = lean_ctor_get(v_toCommandContextInfo_844_, 4);
lean_inc_ref(v_options_845_);
v___x_846_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_845_, v___y_812_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_951_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_951_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_951_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_951_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
uint8_t v___x_851_; 
v___x_851_ = l_Lean_Linter_getLinterValue(v___x_807_, v_a_847_);
lean_dec(v_a_847_);
if (v___x_851_ == 0)
{
lean_object* v___x_853_; 
lean_del_object(v___x_835_);
lean_dec(v___x_827_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_805_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_805_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
else
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Syntax_getId(v___x_827_);
lean_dec(v___x_827_);
if (lean_obj_tag(v___x_855_) == 1)
{
lean_object* v_pre_856_; lean_object* v_str_857_; lean_object* v_ty_859_; lean_object* v___y_860_; lean_object* v___y_861_; 
v_pre_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_pre_856_);
v_str_857_ = lean_ctor_get(v___x_855_, 1);
lean_inc_ref(v_str_857_);
if (lean_obj_tag(v_pre_856_) == 0)
{
lean_del_object(v___x_849_);
if (lean_obj_tag(v_expectedType_x3f_817_) == 1)
{
lean_object* v_val_918_; 
lean_del_object(v___x_823_);
v_val_918_ = lean_ctor_get(v_expectedType_x3f_817_, 0);
lean_inc(v_val_918_);
v_ty_859_ = v_val_918_;
v___y_860_ = v___y_811_;
v___y_861_ = v___y_812_;
goto v___jp_858_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_inc_ref(v_expr_815_);
v___x_919_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_919_, 0, v_expr_815_);
lean_inc_ref(v_ci_808_);
lean_inc_ref(v_i_814_);
v___x_920_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_814_, v_ci_808_, v___x_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; 
lean_del_object(v___x_823_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v_ty_859_ = v_a_921_;
v___y_860_ = v___y_811_;
v___y_861_ = v___y_812_;
goto v___jp_858_;
}
else
{
lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_str_857_);
lean_dec_ref_known(v___x_855_, 2);
lean_del_object(v___x_835_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
v_isSharedCheck_942_ = !lean_is_exclusive(v_val_821_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; lean_object* v_unused_944_; 
v_unused_943_ = lean_ctor_get(v_val_821_, 1);
lean_dec(v_unused_943_);
v_unused_944_ = lean_ctor_get(v_val_821_, 0);
lean_dec(v_unused_944_);
v___x_923_ = v_val_821_;
v_isShared_924_ = v_isSharedCheck_942_;
goto v_resetjp_922_;
}
else
{
lean_dec(v_val_821_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_942_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_941_; 
v_a_925_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_941_ == 0)
{
v___x_927_ = v___x_920_;
v_isShared_928_ = v_isSharedCheck_941_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_920_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_941_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_ref_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v_ref_929_ = lean_ctor_get(v___y_811_, 7);
v___x_930_ = lean_io_error_to_string(v_a_925_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 3);
lean_ctor_set(v___x_823_, 0, v___x_930_);
v___x_932_ = v___x_823_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_940_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = l_Lean_MessageData_ofFormat(v___x_932_);
lean_inc(v_ref_929_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___x_933_);
lean_ctor_set(v___x_923_, 0, v_ref_929_);
v___x_935_ = v___x_923_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_ref_929_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_935_);
v___x_937_ = v___x_927_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
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
lean_object* v___x_946_; 
lean_dec_ref(v_str_857_);
lean_dec_ref_known(v___x_855_, 2);
lean_dec(v_pre_856_);
lean_del_object(v___x_835_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_805_);
v___x_946_ = v___x_849_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_805_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
v___jp_858_:
{
lean_object* v___f_862_; lean_object* v___x_863_; 
v___f_862_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_862_, 0, v_ty_859_);
lean_inc_ref(v_i_814_);
v___x_863_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_814_, v_ci_808_, v___f_862_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_835_);
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_894_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_894_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_894_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Expr_getAppFn_x27(v_a_864_);
lean_dec(v_a_864_);
if (lean_obj_tag(v___x_868_) == 4)
{
lean_object* v_declName_869_; lean_object* v___x_870_; lean_object* v_env_871_; lean_object* v___x_872_; 
v_declName_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_declName_869_);
lean_dec_ref_known(v___x_868_, 2);
v___x_870_ = lean_st_ref_get(v___y_861_);
v_env_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc_ref(v_env_871_);
lean_dec(v___x_870_);
v___x_872_ = l_Lean_Environment_find_x3f(v_env_871_, v_declName_869_, v___x_826_);
if (lean_obj_tag(v___x_872_) == 1)
{
lean_object* v_val_873_; 
v_val_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___x_872_, 1);
if (lean_obj_tag(v_val_873_) == 5)
{
lean_object* v_val_874_; lean_object* v_ctors_875_; lean_object* v___x_876_; 
lean_del_object(v___x_866_);
v_val_874_ = lean_ctor_get(v_val_873_, 0);
lean_inc_ref(v_val_874_);
lean_dec_ref_known(v_val_873_, 1);
v_ctors_875_ = lean_ctor_get(v_val_874_, 4);
lean_inc(v_ctors_875_);
lean_dec_ref(v_val_874_);
v___x_876_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_857_, v_val_804_, v_info_809_, v___x_855_, v_val_821_, v___x_826_, v_ctors_875_, v___x_805_, v___y_861_);
lean_dec(v_ctors_875_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_str_857_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v___x_876_, 0);
lean_dec(v_unused_884_);
v___x_878_ = v___x_876_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_dec(v___x_876_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_805_);
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_805_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
else
{
return v___x_876_;
}
}
else
{
lean_object* v___x_886_; 
lean_dec(v_val_873_);
lean_dec_ref(v_str_857_);
lean_dec_ref_known(v___x_855_, 2);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_805_);
v___x_886_ = v___x_866_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_805_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v___x_889_; 
lean_dec(v___x_872_);
lean_dec_ref(v_str_857_);
lean_dec_ref_known(v___x_855_, 2);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_805_);
v___x_889_ = v___x_866_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_805_);
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
lean_dec_ref(v___x_868_);
lean_dec_ref(v_str_857_);
lean_dec_ref_known(v___x_855_, 2);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_805_);
v___x_892_ = v___x_866_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_805_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref(v_str_857_);
lean_dec_ref_known(v___x_855_, 2);
lean_dec_ref_known(v_info_809_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_val_821_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; 
v_unused_916_ = lean_ctor_get(v_val_821_, 1);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_val_821_, 0);
lean_dec(v_unused_917_);
v___x_896_ = v_val_821_;
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
else
{
lean_dec(v_val_821_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_915_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_914_; 
v_a_898_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_914_ == 0)
{
v___x_900_ = v___x_863_;
v_isShared_901_ = v_isSharedCheck_914_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_863_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_914_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_ref_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v_ref_902_ = lean_ctor_get(v___y_860_, 7);
v___x_903_ = lean_io_error_to_string(v_a_898_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 3);
lean_ctor_set(v___x_835_, 0, v___x_903_);
v___x_905_ = v___x_835_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_913_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Lean_MessageData_ofFormat(v___x_905_);
lean_inc(v_ref_902_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_906_);
lean_ctor_set(v___x_896_, 0, v_ref_902_);
v___x_908_ = v___x_896_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_ref_902_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_908_);
v___x_910_ = v___x_900_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
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
lean_dec(v___x_855_);
lean_del_object(v___x_835_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_805_);
v___x_949_ = v___x_849_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_805_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_del_object(v___x_835_);
lean_dec(v___x_827_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
v_a_952_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_846_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_846_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
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
lean_object* v___x_961_; 
lean_dec(v___x_827_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
lean_ctor_set(v___x_835_, 0, v___x_805_);
v___x_961_ = v___x_835_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_805_);
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
lean_dec(v_val_833_);
lean_dec(v___x_827_);
lean_del_object(v___x_823_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 0);
lean_ctor_set(v___x_835_, 0, v___x_805_);
v___x_964_ = v___x_835_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_805_);
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
}
else
{
lean_object* v___x_968_; 
lean_dec(v___x_832_);
lean_dec(v___x_827_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_805_);
v___x_968_ = v___x_823_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_805_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v___x_971_; 
lean_dec(v___x_828_);
lean_dec(v___x_827_);
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_805_);
v___x_971_ = v___x_823_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_805_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_object* v___x_974_; 
lean_dec(v_val_821_);
lean_dec_ref_known(v_info_809_, 1);
lean_dec_ref(v_ci_808_);
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 0);
lean_ctor_set(v___x_823_, 0, v___x_805_);
v___x_974_ = v___x_823_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_805_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v___x_820_);
lean_dec_ref(v_ci_808_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_info_809_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_info_809_, 0);
lean_dec(v_unused_984_);
v___x_978_ = v_info_809_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_dec(v_info_809_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 0);
lean_ctor_set(v___x_978_, 0, v___x_805_);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_805_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_ci_808_);
v_isSharedCheck_991_ = !lean_is_exclusive(v_info_809_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_info_809_, 0);
lean_dec(v_unused_992_);
v___x_986_ = v_info_809_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_dec(v_info_809_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 0);
lean_ctor_set(v___x_986_, 0, v___x_805_);
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_805_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
else
{
lean_object* v___x_993_; 
lean_dec_ref(v_info_809_);
lean_dec_ref(v_ci_808_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_805_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_994_, lean_object* v___x_995_, lean_object* v_val_996_, lean_object* v___x_997_, lean_object* v_ci_998_, lean_object* v_info_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_994_, v___x_995_, v_val_996_, v___x_997_, v_ci_998_, v_info_999_, v_x_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec_ref(v_x_1000_);
lean_dec_ref(v___x_997_);
lean_dec_ref(v_val_996_);
lean_dec(v_val_994_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_1005_, lean_object* v_ci_1006_, lean_object* v_i_1007_, lean_object* v_cs_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; 
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
v___x_1013_ = lean_apply_6(v_postNode_1005_, v_ci_1006_, v_i_1007_, v_cs_1008_, v___y_1010_, v___y_1011_, lean_box(0));
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1014_, lean_object* v_ci_1015_, lean_object* v_i_1016_, lean_object* v_cs_1017_, lean_object* v_x_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1014_, v_ci_1015_, v_i_1016_, v_cs_1017_, v_x_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v_x_1018_);
return v_res_1022_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_instMonadEIO(lean_box(0));
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_toApplicative_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1063_; 
v___x_1030_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1031_ = l_StateRefT_x27_instMonad___redArg(v___x_1030_);
v_toApplicative_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v___x_1031_, 1);
lean_dec(v_unused_1064_);
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1063_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_toApplicative_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1063_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_toFunctor_1036_; lean_object* v_toSeq_1037_; lean_object* v_toSeqLeft_1038_; lean_object* v_toSeqRight_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1061_; 
v_toFunctor_1036_ = lean_ctor_get(v_toApplicative_1032_, 0);
v_toSeq_1037_ = lean_ctor_get(v_toApplicative_1032_, 2);
v_toSeqLeft_1038_ = lean_ctor_get(v_toApplicative_1032_, 3);
v_toSeqRight_1039_ = lean_ctor_get(v_toApplicative_1032_, 4);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_toApplicative_1032_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_toApplicative_1032_, 1);
lean_dec(v_unused_1062_);
v___x_1041_ = v_toApplicative_1032_;
v_isShared_1042_ = v_isSharedCheck_1061_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_toSeqRight_1039_);
lean_inc(v_toSeqLeft_1038_);
lean_inc(v_toSeq_1037_);
lean_inc(v_toFunctor_1036_);
lean_dec(v_toApplicative_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1061_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1052_; 
v___f_1043_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1044_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1036_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toFunctor_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toFunctor_1036_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___f_1045_);
lean_ctor_set(v___x_1047_, 1, v___f_1046_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeqRight_1039_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeqLeft_1038_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toSeq_1037_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v___f_1048_);
lean_ctor_set(v___x_1041_, 3, v___f_1049_);
lean_ctor_set(v___x_1041_, 2, v___f_1050_);
lean_ctor_set(v___x_1041_, 1, v___f_1043_);
lean_ctor_set(v___x_1041_, 0, v___x_1047_);
v___x_1052_ = v___x_1041_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___f_1048_);
v___x_1052_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___f_1044_);
lean_ctor_set(v___x_1034_, 0, v___x_1052_);
v___x_1054_ = v___x_1034_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___f_1044_);
v___x_1054_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_18817__overap_1057_; lean_object* v___x_1058_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = l_instInhabitedOfMonad___redArg(v___x_1054_, v___x_1055_);
v___x_18817__overap_1057_ = lean_panic_fn_borrowed(v___x_1056_, v_msg_1026_);
lean_dec(v___x_1056_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
v___x_1058_ = lean_apply_3(v___x_18817__overap_1057_, v___y_1027_, v___y_1028_, lean_box(0));
return v___x_1058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1069_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1074_ = lean_unsigned_to_nat(21u);
v___x_1075_ = lean_unsigned_to_nat(65u);
v___x_1076_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1077_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1078_ = l_mkPanicMessageWithDecl(v___x_1077_, v___x_1076_, v___x_1075_, v___x_1074_, v___x_1073_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1079_, lean_object* v_postNode_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
switch(lean_obj_tag(v_x_1082_))
{
case 0:
{
lean_object* v_i_1086_; lean_object* v_t_1087_; lean_object* v___x_1088_; 
v_i_1086_ = lean_ctor_get(v_x_1082_, 0);
lean_inc_ref(v_i_1086_);
v_t_1087_ = lean_ctor_get(v_x_1082_, 1);
lean_inc_ref(v_t_1087_);
lean_dec_ref_known(v_x_1082_, 2);
v___x_1088_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1086_, v_x_1081_);
v_x_1081_ = v___x_1088_;
v_x_1082_ = v_t_1087_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1081_) == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec_ref_known(v_x_1082_, 2);
lean_dec_ref(v_postNode_1080_);
lean_dec_ref(v_preNode_1079_);
v___x_1090_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1091_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1090_, v___y_1083_, v___y_1084_);
return v___x_1091_;
}
else
{
lean_object* v_i_1092_; lean_object* v_children_1093_; lean_object* v_val_1094_; lean_object* v___x_1095_; 
v_i_1092_ = lean_ctor_get(v_x_1082_, 0);
lean_inc_ref_n(v_i_1092_, 2);
v_children_1093_ = lean_ctor_get(v_x_1082_, 1);
lean_inc_ref_n(v_children_1093_, 2);
lean_dec_ref_known(v_x_1082_, 2);
v_val_1094_ = lean_ctor_get(v_x_1081_, 0);
lean_inc_n(v_val_1094_, 2);
lean_inc_ref(v_preNode_1079_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
v___x_1095_ = lean_apply_6(v_preNode_1079_, v_val_1094_, v_i_1092_, v_children_1093_, v___y_1083_, v___y_1084_, lean_box(0));
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; uint8_t v___x_1097_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = lean_unbox(v_a_1096_);
lean_dec(v_a_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_preNode_1079_);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v_x_1081_, 0);
lean_dec(v_unused_1123_);
v___x_1099_ = v_x_1081_;
v_isShared_1100_ = v_isSharedCheck_1122_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v_x_1081_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1122_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
v___x_1102_ = lean_apply_7(v_postNode_1080_, v_val_1094_, v_i_1092_, v_children_1093_, v___x_1101_, v___y_1083_, v___y_1084_, lean_box(0));
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_a_1103_);
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_1099_);
v_a_1114_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1102_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1102_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1124_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1081_, v_i_1092_);
v___x_1125_ = l_Lean_PersistentArray_toList___redArg(v_children_1093_);
v___x_1126_ = lean_box(0);
lean_inc_ref(v_postNode_1080_);
v___x_1127_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1079_, v_postNode_1080_, v___x_1124_, v___x_1125_, v___x_1126_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
v___x_1129_ = lean_apply_7(v_postNode_1080_, v_val_1094_, v_i_1092_, v_children_1093_, v_a_1128_, v___y_1083_, v___y_1084_, lean_box(0));
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1138_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1138_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_a_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
v_a_1139_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1129_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1129_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_val_1094_);
lean_dec_ref(v_children_1093_);
lean_dec_ref(v_i_1092_);
lean_dec_ref(v_postNode_1080_);
v_a_1147_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1127_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1127_);
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
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_val_1094_);
lean_dec_ref(v_children_1093_);
lean_dec_ref(v_i_1092_);
lean_dec_ref_known(v_x_1081_, 1);
lean_dec_ref(v_postNode_1080_);
lean_dec_ref(v_preNode_1079_);
v_a_1155_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1095_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1095_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
default: 
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_x_1081_);
lean_dec_ref(v_postNode_1080_);
lean_dec_ref(v_preNode_1079_);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_x_1082_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_x_1082_, 0);
lean_dec(v_unused_1171_);
v___x_1164_ = v_x_1082_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v_x_1082_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_box(0);
if (v_isShared_1165_ == 0)
{
lean_ctor_set_tag(v___x_1164_, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1172_, lean_object* v_postNode_1173_, lean_object* v___x_1174_, lean_object* v_x_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
if (lean_obj_tag(v_x_1175_) == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
lean_dec(v___x_1174_);
lean_dec_ref(v_postNode_1173_);
lean_dec_ref(v_preNode_1172_);
v___x_1180_ = l_List_reverse___redArg(v_x_1176_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
else
{
lean_object* v_head_1182_; lean_object* v_tail_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1201_; 
v_head_1182_ = lean_ctor_get(v_x_1175_, 0);
v_tail_1183_ = lean_ctor_get(v_x_1175_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_x_1175_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1185_ = v_x_1175_;
v_isShared_1186_ = v_isSharedCheck_1201_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_tail_1183_);
lean_inc(v_head_1182_);
lean_dec(v_x_1175_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1201_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; 
lean_inc(v___x_1174_);
lean_inc_ref(v_postNode_1173_);
lean_inc_ref(v_preNode_1172_);
v___x_1187_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1172_, v_postNode_1173_, v___x_1174_, v_head_1182_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_x_1176_);
lean_ctor_set(v___x_1185_, 0, v_a_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1188_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_x_1176_);
v___x_1190_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
v_x_1175_ = v_tail_1183_;
v_x_1176_ = v___x_1190_;
goto _start;
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_del_object(v___x_1185_);
lean_dec(v_tail_1183_);
lean_dec(v_x_1176_);
lean_dec(v___x_1174_);
lean_dec_ref(v_postNode_1173_);
lean_dec_ref(v_preNode_1172_);
v_a_1193_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1187_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1187_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1202_, lean_object* v_postNode_1203_, lean_object* v___x_1204_, lean_object* v_x_1205_, lean_object* v_x_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1202_, v_postNode_1203_, v___x_1204_, v_x_1205_, v_x_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1211_, lean_object* v_postNode_1212_, lean_object* v_x_1213_, lean_object* v_x_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1211_, v_postNode_1212_, v_x_1213_, v_x_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1219_, lean_object* v_postNode_1220_, lean_object* v_ctx_x3f_1221_, lean_object* v_t_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___f_1226_; lean_object* v___x_1227_; 
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1226_, 0, v_postNode_1220_);
v___x_1227_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1219_, v___f_1226_, v_ctx_x3f_1221_, v_t_1222_, v___y_1223_, v___y_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1227_, 0);
lean_dec(v_unused_1236_);
v___x_1229_ = v___x_1227_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v___x_1227_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_box(0);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
v_a_1237_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1227_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1227_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1245_, lean_object* v_postNode_1246_, lean_object* v_ctx_x3f_1247_, lean_object* v_t_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1245_, v_postNode_1246_, v_ctx_x3f_1247_, v_t_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1253_, lean_object* v_val_1254_, lean_object* v_val_1255_, lean_object* v_as_1256_, size_t v_sz_1257_, size_t v_i_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_usize_dec_lt(v_i_1258_, v_sz_1257_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v_val_1255_);
lean_dec(v_val_1254_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v_b_1259_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___f_1269_; lean_object* v_a_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1265_ = lean_box(v___x_1253_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1266_, 0, v___x_1265_);
v___x_1267_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1268_ = lean_box(0);
lean_inc_ref(v_val_1255_);
lean_inc(v_val_1254_);
v___f_1269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1269_, 0, v_val_1254_);
lean_closure_set(v___f_1269_, 1, v___x_1268_);
lean_closure_set(v___f_1269_, 2, v_val_1255_);
lean_closure_set(v___f_1269_, 3, v___x_1267_);
v_a_1270_ = lean_array_uget_borrowed(v_as_1256_, v_i_1258_);
v___x_1271_ = lean_box(0);
lean_inc(v_a_1270_);
v___x_1272_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1266_, v___f_1269_, v___x_1271_, v_a_1270_, v___y_1260_, v___y_1261_);
if (lean_obj_tag(v___x_1272_) == 0)
{
size_t v___x_1273_; size_t v___x_1274_; 
lean_dec_ref_known(v___x_1272_, 1);
v___x_1273_ = ((size_t)1ULL);
v___x_1274_ = lean_usize_add(v_i_1258_, v___x_1273_);
v_i_1258_ = v___x_1274_;
v_b_1259_ = v___x_1268_;
goto _start;
}
else
{
lean_dec_ref(v_val_1255_);
lean_dec(v_val_1254_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1276_, lean_object* v_val_1277_, lean_object* v_val_1278_, lean_object* v_as_1279_, lean_object* v_sz_1280_, lean_object* v_i_1281_, lean_object* v_b_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v___x_23456__boxed_1286_; size_t v_sz_boxed_1287_; size_t v_i_boxed_1288_; lean_object* v_res_1289_; 
v___x_23456__boxed_1286_ = lean_unbox(v___x_1276_);
v_sz_boxed_1287_ = lean_unbox_usize(v_sz_1280_);
lean_dec(v_sz_1280_);
v_i_boxed_1288_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23456__boxed_1286_, v_val_1277_, v_val_1278_, v_as_1279_, v_sz_boxed_1287_, v_i_boxed_1288_, v_b_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_as_1279_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
return v_x_1290_;
}
else
{
lean_object* v_key_1292_; lean_object* v_value_1293_; lean_object* v_tail_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_key_1292_ = lean_ctor_get(v_x_1291_, 0);
v_value_1293_ = lean_ctor_get(v_x_1291_, 1);
v_tail_1294_ = lean_ctor_get(v_x_1291_, 2);
lean_inc(v_value_1293_);
lean_inc(v_key_1292_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_key_1292_);
lean_ctor_set(v___x_1295_, 1, v_value_1293_);
v___x_1296_ = lean_array_push(v_x_1290_, v___x_1295_);
v_x_1290_ = v___x_1296_;
v_x_1291_ = v_tail_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1298_, v_x_1299_);
lean_dec(v_x_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1301_, size_t v_i_1302_, size_t v_stop_1303_, lean_object* v_b_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_eq(v_i_1302_, v_stop_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; 
v___x_1306_ = lean_array_uget_borrowed(v_as_1301_, v_i_1302_);
v___x_1307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1304_, v___x_1306_);
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = lean_usize_add(v_i_1302_, v___x_1308_);
v_i_1302_ = v___x_1309_;
v_b_1304_ = v___x_1307_;
goto _start;
}
else
{
return v_b_1304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1311_, lean_object* v_i_1312_, lean_object* v_stop_1313_, lean_object* v_b_1314_){
_start:
{
size_t v_i_boxed_1315_; size_t v_stop_boxed_1316_; lean_object* v_res_1317_; 
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_stop_boxed_1316_ = lean_unbox_usize(v_stop_1313_);
lean_dec(v_stop_1313_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1311_, v_i_boxed_1315_, v_stop_boxed_1316_, v_b_1314_);
lean_dec_ref(v_as_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; lean_object* v_scopes_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v_opts_1325_; lean_object* v___x_1326_; 
v___x_1321_ = lean_st_ref_get(v___y_1319_);
v_scopes_1322_ = lean_ctor_get(v___x_1321_, 2);
lean_inc(v_scopes_1322_);
lean_dec(v___x_1321_);
v___x_1323_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1324_ = l_List_head_x21___redArg(v___x_1323_, v_scopes_1322_);
lean_dec(v_scopes_1322_);
v_opts_1325_ = lean_ctor_get(v___x_1324_, 1);
lean_inc_ref(v_opts_1325_);
lean_dec(v___x_1324_);
v___x_1326_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1325_, v___y_1319_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1330_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_box(0);
v___x_1332_ = lean_unsigned_to_nat(16u);
v___x_1333_ = lean_mk_array(v___x_1332_, v___x_1331_);
return v___x_1333_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___x_1334_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1412_; 
v___x_1341_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1338_, v___y_1339_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1412_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1412_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1347_ = l_Lean_Linter_getLinterValue(v___x_1346_, v_a_1342_);
lean_dec(v_a_1342_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_box(0);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1348_);
v___x_1350_ = v___x_1344_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
uint8_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = 0;
v___x_1353_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1337_, v___x_1352_);
if (lean_obj_tag(v___x_1353_) == 1)
{
lean_object* v_val_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v_infoState_1359_; lean_object* v_trees_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; size_t v_sz_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
lean_del_object(v___x_1344_);
v_val_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_val_1354_);
lean_dec_ref_known(v___x_1353_, 1);
v___x_1355_ = lean_st_ref_get(v___y_1339_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1358_ = lean_st_mk_ref(v___x_1357_);
v_infoState_1359_ = lean_ctor_get(v___x_1355_, 8);
lean_inc_ref(v_infoState_1359_);
lean_dec(v___x_1355_);
v_trees_1360_ = lean_ctor_get(v_infoState_1359_, 2);
lean_inc_ref(v_trees_1360_);
lean_dec_ref(v_infoState_1359_);
v___x_1361_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1360_);
lean_dec_ref(v_trees_1360_);
v___x_1362_ = lean_box(0);
v_sz_1363_ = lean_array_size(v___x_1361_);
v___x_1364_ = ((size_t)0ULL);
lean_inc(v___x_1358_);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1347_, v___x_1358_, v_val_1354_, v___x_1361_, v_sz_1363_, v___x_1364_, v___x_1362_, v___y_1338_, v___y_1339_);
lean_dec_ref(v___x_1361_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; lean_object* v___y_1368_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1392_; lean_object* v_size_1398_; lean_object* v_buckets_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
lean_dec_ref_known(v___x_1365_, 1);
v___x_1366_ = lean_st_ref_get(v___x_1358_);
lean_dec(v___x_1358_);
v_size_1398_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_size_1398_);
v_buckets_1399_ = lean_ctor_get(v___x_1366_, 1);
lean_inc_ref(v_buckets_1399_);
lean_dec(v___x_1366_);
v___x_1400_ = lean_mk_empty_array_with_capacity(v_size_1398_);
lean_dec(v_size_1398_);
v___x_1401_ = lean_array_get_size(v_buckets_1399_);
v___x_1402_ = lean_nat_dec_lt(v___x_1356_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v_buckets_1399_);
v___y_1392_ = v___x_1400_;
goto v___jp_1391_;
}
else
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_nat_dec_le(v___x_1401_, v___x_1401_);
if (v___x_1403_ == 0)
{
if (v___x_1402_ == 0)
{
lean_dec_ref(v_buckets_1399_);
v___y_1392_ = v___x_1400_;
goto v___jp_1391_;
}
else
{
size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_usize_of_nat(v___x_1401_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1399_, v___x_1364_, v___x_1404_, v___x_1400_);
lean_dec_ref(v_buckets_1399_);
v___y_1392_ = v___x_1405_;
goto v___jp_1391_;
}
}
else
{
size_t v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_usize_of_nat(v___x_1401_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1399_, v___x_1364_, v___x_1406_, v___x_1400_);
lean_dec_ref(v_buckets_1399_);
v___y_1392_ = v___x_1407_;
goto v___jp_1391_;
}
}
v___jp_1367_:
{
size_t v_sz_1369_; lean_object* v___x_1370_; 
v_sz_1369_ = lean_array_size(v___y_1368_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1368_, v_sz_1369_, v___x_1364_, v___x_1362_, v___y_1338_, v___y_1339_);
lean_dec_ref(v___y_1368_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1370_, 0);
lean_dec(v_unused_1378_);
v___x_1372_ = v___x_1370_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_dec(v___x_1370_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1362_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1362_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
return v___x_1370_;
}
}
v___jp_1379_:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1380_, v___y_1382_, v___y_1381_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec(v___y_1380_);
v___y_1368_ = v___x_1384_;
goto v___jp_1367_;
}
v___jp_1385_:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_nat_dec_le(v___y_1389_, v___y_1387_);
if (v___x_1390_ == 0)
{
lean_dec(v___y_1387_);
lean_inc(v___y_1389_);
v___y_1380_ = v___y_1386_;
v___y_1381_ = v___y_1389_;
v___y_1382_ = v___y_1388_;
v___y_1383_ = v___y_1389_;
goto v___jp_1379_;
}
else
{
v___y_1380_ = v___y_1386_;
v___y_1381_ = v___y_1389_;
v___y_1382_ = v___y_1388_;
v___y_1383_ = v___y_1387_;
goto v___jp_1379_;
}
}
v___jp_1391_:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = lean_array_get_size(v___y_1392_);
v___x_1394_ = lean_nat_dec_eq(v___x_1393_, v___x_1356_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(1u);
v___x_1396_ = lean_nat_sub(v___x_1393_, v___x_1395_);
v___x_1397_ = lean_nat_dec_le(v___x_1356_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_inc(v___x_1396_);
v___y_1386_ = v___x_1393_;
v___y_1387_ = v___x_1396_;
v___y_1388_ = v___y_1392_;
v___y_1389_ = v___x_1396_;
goto v___jp_1385_;
}
else
{
v___y_1386_ = v___x_1393_;
v___y_1387_ = v___x_1396_;
v___y_1388_ = v___y_1392_;
v___y_1389_ = v___x_1356_;
goto v___jp_1385_;
}
}
else
{
v___y_1368_ = v___y_1392_;
goto v___jp_1367_;
}
}
}
else
{
lean_dec(v___x_1358_);
return v___x_1365_;
}
}
else
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
lean_dec(v___x_1353_);
v___x_1408_ = lean_box(0);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1408_);
v___x_1410_ = v___x_1344_;
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
uint8_t v___x_23748__boxed_1468_; lean_object* v_res_1469_; 
v___x_23748__boxed_1468_ = lean_unbox(v___x_1460_);
v_res_1469_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1455_, v_val_1456_, v_info_1457_, v___x_1458_, v_val_1459_, v___x_23748__boxed_1468_, v_as_1461_, v_as_x27_1462_, v_b_1463_, v_a_1464_, v___y_1465_, v___y_1466_);
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
