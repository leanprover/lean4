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
uint8_t v___y_21729__boxed_227_; uint8_t v_suppressElabErrors_boxed_228_; uint8_t v_res_229_; lean_object* v_r_230_; 
v___y_21729__boxed_227_ = lean_unbox(v___y_224_);
v_suppressElabErrors_boxed_228_ = lean_unbox(v_suppressElabErrors_225_);
v_res_229_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21729__boxed_227_, v_suppressElabErrors_boxed_228_, v_x_226_);
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
uint8_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; uint8_t v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; uint8_t v___y_356_; uint8_t v___y_357_; lean_object* v___y_358_; uint8_t v___y_359_; lean_object* v___y_360_; uint8_t v___y_384_; uint8_t v___y_385_; uint8_t v___y_386_; lean_object* v___y_387_; lean_object* v___y_388_; uint8_t v___y_392_; uint8_t v___y_393_; uint8_t v___y_394_; uint8_t v___x_409_; uint8_t v___y_411_; uint8_t v___y_412_; uint8_t v___y_413_; uint8_t v___y_415_; uint8_t v___x_427_; 
v___x_409_ = 2;
v___x_427_ = l_Lean_instBEqMessageSeverity_beq(v_severity_286_, v___x_409_);
if (v___x_427_ == 0)
{
v___y_415_ = v___x_427_;
goto v___jp_414_;
}
else
{
uint8_t v___x_428_; 
lean_inc_ref(v_msgData_285_);
v___x_428_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_285_);
v___y_415_ = v___x_428_;
goto v___jp_414_;
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
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_338_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_338_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_338_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_338_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v_currNamespace_308_; lean_object* v_openDecls_309_; lean_object* v_env_310_; lean_object* v_messages_311_; lean_object* v_scopes_312_; lean_object* v_usedQuotCtxts_313_; lean_object* v_nextMacroScope_314_; lean_object* v_maxRecDepth_315_; lean_object* v_ngen_316_; lean_object* v_auxDeclNGen_317_; lean_object* v_infoState_318_; lean_object* v_traceState_319_; lean_object* v_snapshotTasks_320_; lean_object* v_prevLinterStates_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_337_; 
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
v_prevLinterStates_321_ = lean_ctor_get(v___x_307_, 11);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_337_ == 0)
{
v___x_323_ = v___x_307_;
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_prevLinterStates_321_);
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
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_337_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v_currNamespace_308_);
lean_ctor_set(v___x_325_, 1, v_openDecls_309_);
v___x_326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___y_298_);
lean_inc_ref(v___y_294_);
lean_inc_ref(v___y_296_);
v___x_327_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_327_, 0, v___y_296_);
lean_ctor_set(v___x_327_, 1, v___y_293_);
lean_ctor_set(v___x_327_, 2, v___y_295_);
lean_ctor_set(v___x_327_, 3, v___y_294_);
lean_ctor_set(v___x_327_, 4, v___x_326_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*5, v___y_292_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*5 + 1, v___y_297_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*5 + 2, v_isSilent_287_);
v___x_328_ = l_Lean_MessageLog_add(v___x_327_, v_messages_311_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 1, v___x_328_);
v___x_330_ = v___x_323_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_env_310_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_scopes_312_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_usedQuotCtxts_313_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_nextMacroScope_314_);
lean_ctor_set(v_reuseFailAlloc_336_, 5, v_maxRecDepth_315_);
lean_ctor_set(v_reuseFailAlloc_336_, 6, v_ngen_316_);
lean_ctor_set(v_reuseFailAlloc_336_, 7, v_auxDeclNGen_317_);
lean_ctor_set(v_reuseFailAlloc_336_, 8, v_infoState_318_);
lean_ctor_set(v_reuseFailAlloc_336_, 9, v_traceState_319_);
lean_ctor_set(v_reuseFailAlloc_336_, 10, v_snapshotTasks_320_);
lean_ctor_set(v_reuseFailAlloc_336_, 11, v_prevLinterStates_321_);
v___x_330_ = v_reuseFailAlloc_336_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_331_ = lean_st_ref_set(v___y_299_, v___x_330_);
v___x_332_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_332_);
v___x_334_ = v___x_305_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec(v_a_301_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_293_);
v_a_339_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_302_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_302_);
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
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___y_298_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_293_);
v_a_347_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_300_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_300_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
v___jp_355_:
{
lean_object* v_fileName_361_; lean_object* v_fileMap_362_; uint8_t v_suppressElabErrors_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_382_; 
v_fileName_361_ = lean_ctor_get(v___y_288_, 0);
v_fileMap_362_ = lean_ctor_get(v___y_288_, 1);
v_suppressElabErrors_363_ = lean_ctor_get_uint8(v___y_288_, sizeof(void*)*10);
v___x_364_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_285_);
v___x_365_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v___x_364_, v___y_289_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_382_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
lean_inc_ref_n(v_fileMap_362_, 2);
v___x_370_ = l_Lean_FileMap_toPosition(v_fileMap_362_, v___y_358_);
lean_dec(v___y_358_);
v___x_371_ = l_Lean_FileMap_toPosition(v_fileMap_362_, v___y_360_);
lean_dec(v___y_360_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___x_373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_363_ == 0)
{
lean_del_object(v___x_368_);
v___y_292_ = v___y_357_;
v___y_293_ = v___x_370_;
v___y_294_ = v___x_373_;
v___y_295_ = v___x_372_;
v___y_296_ = v_fileName_361_;
v___y_297_ = v___y_359_;
v___y_298_ = v_a_366_;
v___y_299_ = v___y_289_;
goto v___jp_291_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___f_376_; uint8_t v___x_377_; 
v___x_374_ = lean_box(v___y_356_);
v___x_375_ = lean_box(v_suppressElabErrors_363_);
v___f_376_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0___boxed), 3, 2);
lean_closure_set(v___f_376_, 0, v___x_374_);
lean_closure_set(v___f_376_, 1, v___x_375_);
lean_inc(v_a_366_);
v___x_377_ = l_Lean_MessageData_hasTag(v___f_376_, v_a_366_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; lean_object* v___x_380_; 
lean_dec_ref_known(v___x_372_, 1);
lean_dec_ref(v___x_370_);
lean_dec(v_a_366_);
v___x_378_ = lean_box(0);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_378_);
v___x_380_ = v___x_368_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
else
{
lean_del_object(v___x_368_);
v___y_292_ = v___y_357_;
v___y_293_ = v___x_370_;
v___y_294_ = v___x_373_;
v___y_295_ = v___x_372_;
v___y_296_ = v_fileName_361_;
v___y_297_ = v___y_359_;
v___y_298_ = v_a_366_;
v___y_299_ = v___y_289_;
goto v___jp_291_;
}
}
}
}
v___jp_383_:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Syntax_getTailPos_x3f(v___y_387_, v___y_385_);
lean_dec(v___y_387_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_inc(v___y_388_);
v___y_356_ = v___y_384_;
v___y_357_ = v___y_385_;
v___y_358_ = v___y_388_;
v___y_359_ = v___y_386_;
v___y_360_ = v___y_388_;
goto v___jp_355_;
}
else
{
lean_object* v_val_390_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_389_, 1);
v___y_356_ = v___y_384_;
v___y_357_ = v___y_385_;
v___y_358_ = v___y_388_;
v___y_359_ = v___y_386_;
v___y_360_ = v_val_390_;
goto v___jp_355_;
}
}
v___jp_391_:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Elab_Command_getRef___redArg(v___y_288_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v_ref_397_; lean_object* v___x_398_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v___x_395_, 1);
v_ref_397_ = l_Lean_replaceRef(v_ref_284_, v_a_396_);
lean_dec(v_a_396_);
v___x_398_ = l_Lean_Syntax_getPos_x3f(v_ref_397_, v___y_393_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___y_384_ = v___y_392_;
v___y_385_ = v___y_393_;
v___y_386_ = v___y_394_;
v___y_387_ = v_ref_397_;
v___y_388_ = v___x_399_;
goto v___jp_383_;
}
else
{
lean_object* v_val_400_; 
v_val_400_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v___x_398_, 1);
v___y_384_ = v___y_392_;
v___y_385_ = v___y_393_;
v___y_386_ = v___y_394_;
v___y_387_ = v_ref_397_;
v___y_388_ = v_val_400_;
goto v___jp_383_;
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_msgData_285_);
v_a_401_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_395_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_395_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
v___jp_410_:
{
if (v___y_413_ == 0)
{
v___y_392_ = v___y_411_;
v___y_393_ = v___y_412_;
v___y_394_ = v_severity_286_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___y_411_;
v___y_393_ = v___y_412_;
v___y_394_ = v___x_409_;
goto v___jp_391_;
}
}
v___jp_414_:
{
if (v___y_415_ == 0)
{
lean_object* v___x_416_; lean_object* v_scopes_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_opts_420_; uint8_t v___x_421_; uint8_t v___x_422_; 
v___x_416_ = lean_st_ref_get(v___y_289_);
v_scopes_417_ = lean_ctor_get(v___x_416_, 2);
lean_inc(v_scopes_417_);
lean_dec(v___x_416_);
v___x_418_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_419_ = l_List_head_x21___redArg(v___x_418_, v_scopes_417_);
lean_dec(v_scopes_417_);
v_opts_420_ = lean_ctor_get(v___x_419_, 1);
lean_inc_ref(v_opts_420_);
lean_dec(v___x_419_);
v___x_421_ = 1;
v___x_422_ = l_Lean_instBEqMessageSeverity_beq(v_severity_286_, v___x_421_);
if (v___x_422_ == 0)
{
lean_dec_ref(v_opts_420_);
v___y_411_ = v___y_415_;
v___y_412_ = v___y_415_;
v___y_413_ = v___x_422_;
goto v___jp_410_;
}
else
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = l_Lean_warningAsError;
v___x_424_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__23(v_opts_420_, v___x_423_);
lean_dec_ref(v_opts_420_);
v___y_411_ = v___y_415_;
v___y_412_ = v___y_415_;
v___y_413_ = v___x_424_;
goto v___jp_410_;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v_msgData_285_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___boxed(lean_object* v_ref_429_, lean_object* v_msgData_430_, lean_object* v_severity_431_, lean_object* v_isSilent_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v_severity_boxed_436_; uint8_t v_isSilent_boxed_437_; lean_object* v_res_438_; 
v_severity_boxed_436_ = lean_unbox(v_severity_431_);
v_isSilent_boxed_437_ = lean_unbox(v_isSilent_432_);
v_res_438_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_429_, v_msgData_430_, v_severity_boxed_436_, v_isSilent_boxed_437_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v_ref_429_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(lean_object* v_ref_439_, lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
uint8_t v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = 1;
v___x_445_ = 0;
v___x_446_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15(v_ref_439_, v_msgData_440_, v___x_444_, v___x_445_, v___y_441_, v___y_442_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11___boxed(lean_object* v_ref_447_, lean_object* v_msgData_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_ref_447_, v_msgData_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v_ref_447_);
return v_res_452_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__0));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__2));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* v_linterOption_459_, lean_object* v_stx_460_, lean_object* v_msg_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_name_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_483_; 
v_name_465_ = lean_ctor_get(v_linterOption_459_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_linterOption_459_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_linterOption_459_, 1);
lean_dec(v_unused_484_);
v___x_467_ = v_linterOption_459_;
v_isShared_468_ = v_isSharedCheck_483_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_name_465_);
lean_dec(v_linterOption_459_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_483_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__1);
lean_inc(v_name_465_);
v___x_470_ = l_Lean_MessageData_ofName(v_name_465_);
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 7);
lean_ctor_set(v___x_467_, 1, v___x_470_);
lean_ctor_set(v___x_467_, 0, v___x_469_);
v___x_472_ = v___x_467_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_470_);
v___x_472_ = v_reuseFailAlloc_482_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_disable_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_473_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v_disable_475_ = l_Lean_MessageData_note(v___x_474_);
v___x_476_ = l_Lean_Linter_linterMessageTag;
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v_msg_461_);
lean_ctor_set(v___x_477_, 1, v_disable_475_);
v___x_478_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_479_, 0, v_name_465_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_inc(v_stx_460_);
v___x_480_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_480_, 0, v_stx_460_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
v___x_481_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_460_, v___x_480_, v___y_462_, v___y_463_);
lean_dec(v_stx_460_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_485_, lean_object* v_stx_486_, lean_object* v_msg_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_485_, v_stx_486_, v_msg_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
return v_res_491_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_497_ = l_Lean_stringToMessageData(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_503_ = l_Lean_stringToMessageData(v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_510_, size_t v_sz_511_, size_t v_i_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_lt(v_i_512_, v_sz_511_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_b_513_);
return v___x_518_;
}
else
{
lean_object* v_a_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_565_; 
v_a_519_ = lean_array_uget(v_as_510_, v_i_512_);
v_snd_520_ = lean_ctor_get(v_a_519_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_519_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v_a_519_, 0);
lean_dec(v_unused_566_);
v___x_522_ = v_a_519_;
v_isShared_523_ = v_isSharedCheck_565_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_dec(v_a_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_565_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_snd_524_; lean_object* v_fst_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_564_; 
v_snd_524_ = lean_ctor_get(v_snd_520_, 1);
v_fst_525_ = lean_ctor_get(v_snd_520_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v_snd_520_);
if (v_isSharedCheck_564_ == 0)
{
v___x_527_ = v_snd_520_;
v_isShared_528_ = v_isSharedCheck_564_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_snd_524_);
lean_inc(v_fst_525_);
lean_dec(v_snd_520_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_564_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_563_; 
v_fst_529_ = lean_ctor_get(v_snd_524_, 0);
v_snd_530_ = lean_ctor_get(v_snd_524_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_snd_524_);
if (v_isSharedCheck_563_ == 0)
{
v___x_532_ = v_snd_524_;
v_isShared_533_ = v_isSharedCheck_563_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_inc(v_fst_529_);
lean_dec(v_snd_524_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_563_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_534_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_536_ = l_Lean_MessageData_ofName(v_fst_529_);
lean_inc_ref(v___x_536_);
if (v_isShared_533_ == 0)
{
lean_ctor_set_tag(v___x_532_, 7);
lean_ctor_set(v___x_532_, 1, v___x_536_);
lean_ctor_set(v___x_532_, 0, v___x_535_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_562_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_528_ == 0)
{
lean_ctor_set_tag(v___x_527_, 7);
lean_ctor_set(v___x_527_, 1, v___x_539_);
lean_ctor_set(v___x_527_, 0, v___x_538_);
v___x_541_ = v___x_527_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___x_539_);
v___x_541_ = v_reuseFailAlloc_561_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = l_Lean_MessageData_ofName(v_snd_530_);
lean_inc_ref(v___x_542_);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 7);
lean_ctor_set(v___x_522_, 1, v___x_542_);
lean_ctor_set(v___x_522_, 0, v___x_541_);
v___x_544_ = v___x_522_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_560_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_536_);
v___x_549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v___x_542_);
v___x_552_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_546_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_534_, v_fst_525_, v___x_554_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; 
lean_dec_ref_known(v___x_555_, 1);
v___x_556_ = lean_box(0);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_512_, v___x_557_);
v_i_512_ = v___x_558_;
v_b_513_ = v___x_556_;
goto _start;
}
else
{
return v___x_555_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_567_, lean_object* v_sz_568_, lean_object* v_i_569_, lean_object* v_b_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
size_t v_sz_boxed_574_; size_t v_i_boxed_575_; lean_object* v_res_576_; 
v_sz_boxed_574_ = lean_unbox_usize(v_sz_568_);
lean_dec(v_sz_568_);
v_i_boxed_575_ = lean_unbox_usize(v_i_569_);
lean_dec(v_i_569_);
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_567_, v_sz_boxed_574_, v_i_boxed_575_, v_b_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v_as_567_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_box(v___x_577_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
uint8_t v___x_22347__boxed_593_; lean_object* v_res_594_; 
v___x_22347__boxed_593_ = lean_unbox(v___x_586_);
v_res_594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22347__boxed_593_, v_x_587_, v_x_588_, v_x_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_x_589_);
lean_dec_ref(v_x_588_);
lean_dec_ref(v_x_587_);
return v_res_594_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_595_, lean_object* v_x_596_){
_start:
{
if (lean_obj_tag(v_x_596_) == 0)
{
uint8_t v___x_597_; 
v___x_597_ = 0;
return v___x_597_;
}
else
{
lean_object* v_key_598_; lean_object* v_tail_599_; uint8_t v___x_600_; 
v_key_598_ = lean_ctor_get(v_x_596_, 0);
v_tail_599_ = lean_ctor_get(v_x_596_, 2);
v___x_600_ = l_Lean_Syntax_instBEqRange_beq(v_key_598_, v_a_595_);
if (v___x_600_ == 0)
{
v_x_596_ = v_tail_599_;
goto _start;
}
else
{
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_602_, v_x_603_);
lean_dec(v_x_603_);
lean_dec_ref(v_a_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_buckets_608_; lean_object* v___x_609_; uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v___x_612_; uint64_t v_fold_613_; uint64_t v___x_614_; uint64_t v___x_615_; uint64_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_buckets_608_ = lean_ctor_get(v_m_606_, 1);
v___x_609_ = lean_array_get_size(v_buckets_608_);
v___x_610_ = l_Lean_Syntax_instHashableRange_hash(v_a_607_);
v___x_611_ = 32ULL;
v___x_612_ = lean_uint64_shift_right(v___x_610_, v___x_611_);
v_fold_613_ = lean_uint64_xor(v___x_610_, v___x_612_);
v___x_614_ = 16ULL;
v___x_615_ = lean_uint64_shift_right(v_fold_613_, v___x_614_);
v___x_616_ = lean_uint64_xor(v_fold_613_, v___x_615_);
v___x_617_ = lean_uint64_to_usize(v___x_616_);
v___x_618_ = lean_usize_of_nat(v___x_609_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_sub(v___x_618_, v___x_619_);
v___x_621_ = lean_usize_land(v___x_617_, v___x_620_);
v___x_622_ = lean_array_uget_borrowed(v_buckets_608_, v___x_621_);
v___x_623_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_607_, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_624_, v_a_625_);
lean_dec_ref(v_a_625_);
lean_dec_ref(v_m_624_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_628_, lean_object* v_b_629_, lean_object* v_x_630_){
_start:
{
if (lean_obj_tag(v_x_630_) == 0)
{
lean_dec(v_b_629_);
lean_dec_ref(v_a_628_);
return v_x_630_;
}
else
{
lean_object* v_key_631_; lean_object* v_value_632_; lean_object* v_tail_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_645_; 
v_key_631_ = lean_ctor_get(v_x_630_, 0);
v_value_632_ = lean_ctor_get(v_x_630_, 1);
v_tail_633_ = lean_ctor_get(v_x_630_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_630_);
if (v_isSharedCheck_645_ == 0)
{
v___x_635_ = v_x_630_;
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_tail_633_);
lean_inc(v_value_632_);
lean_inc(v_key_631_);
lean_dec(v_x_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_645_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint8_t v___x_637_; 
v___x_637_ = l_Lean_Syntax_instBEqRange_beq(v_key_631_, v_a_628_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_628_, v_b_629_, v_tail_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 2, v___x_638_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_key_631_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_value_632_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
else
{
lean_object* v___x_643_; 
lean_dec(v_value_632_);
lean_dec(v_key_631_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 1, v_b_629_);
lean_ctor_set(v___x_635_, 0, v_a_628_);
v___x_643_ = v___x_635_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_628_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_b_629_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_tail_633_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_647_) == 0)
{
return v_x_646_;
}
else
{
lean_object* v_key_648_; lean_object* v_value_649_; lean_object* v_tail_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_673_; 
v_key_648_ = lean_ctor_get(v_x_647_, 0);
v_value_649_ = lean_ctor_get(v_x_647_, 1);
v_tail_650_ = lean_ctor_get(v_x_647_, 2);
v_isSharedCheck_673_ = !lean_is_exclusive(v_x_647_);
if (v_isSharedCheck_673_ == 0)
{
v___x_652_ = v_x_647_;
v_isShared_653_ = v_isSharedCheck_673_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_tail_650_);
lean_inc(v_value_649_);
lean_inc(v_key_648_);
lean_dec(v_x_647_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_673_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; uint64_t v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v_fold_658_; uint64_t v___x_659_; uint64_t v___x_660_; uint64_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_654_ = lean_array_get_size(v_x_646_);
v___x_655_ = l_Lean_Syntax_instHashableRange_hash(v_key_648_);
v___x_656_ = 32ULL;
v___x_657_ = lean_uint64_shift_right(v___x_655_, v___x_656_);
v_fold_658_ = lean_uint64_xor(v___x_655_, v___x_657_);
v___x_659_ = 16ULL;
v___x_660_ = lean_uint64_shift_right(v_fold_658_, v___x_659_);
v___x_661_ = lean_uint64_xor(v_fold_658_, v___x_660_);
v___x_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = lean_usize_of_nat(v___x_654_);
v___x_664_ = ((size_t)1ULL);
v___x_665_ = lean_usize_sub(v___x_663_, v___x_664_);
v___x_666_ = lean_usize_land(v___x_662_, v___x_665_);
v___x_667_ = lean_array_uget_borrowed(v_x_646_, v___x_666_);
lean_inc(v___x_667_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 2, v___x_667_);
v___x_669_ = v___x_652_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_key_648_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_value_649_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v___x_667_);
v___x_669_ = v_reuseFailAlloc_672_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_array_uset(v_x_646_, v___x_666_, v___x_669_);
v_x_646_ = v___x_670_;
v_x_647_ = v_tail_650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_674_, lean_object* v_source_675_, lean_object* v_target_676_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = lean_array_get_size(v_source_675_);
v___x_678_ = lean_nat_dec_lt(v_i_674_, v___x_677_);
if (v___x_678_ == 0)
{
lean_dec_ref(v_source_675_);
lean_dec(v_i_674_);
return v_target_676_;
}
else
{
lean_object* v_es_679_; lean_object* v___x_680_; lean_object* v_source_681_; lean_object* v_target_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_es_679_ = lean_array_fget(v_source_675_, v_i_674_);
v___x_680_ = lean_box(0);
v_source_681_ = lean_array_fset(v_source_675_, v_i_674_, v___x_680_);
v_target_682_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_676_, v_es_679_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_i_674_, v___x_683_);
lean_dec(v_i_674_);
v_i_674_ = v___x_684_;
v_source_675_ = v_source_681_;
v_target_676_ = v_target_682_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_nbuckets_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_687_ = lean_array_get_size(v_data_686_);
v___x_688_ = lean_unsigned_to_nat(2u);
v_nbuckets_689_ = lean_nat_mul(v___x_687_, v___x_688_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_box(0);
v___x_692_ = lean_mk_array(v_nbuckets_689_, v___x_691_);
v___x_693_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_690_, v_data_686_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_694_, lean_object* v_a_695_, lean_object* v_b_696_){
_start:
{
lean_object* v_size_697_; lean_object* v_buckets_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_741_; 
v_size_697_ = lean_ctor_get(v_m_694_, 0);
v_buckets_698_ = lean_ctor_get(v_m_694_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_m_694_);
if (v_isSharedCheck_741_ == 0)
{
v___x_700_ = v_m_694_;
v_isShared_701_ = v_isSharedCheck_741_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_buckets_698_);
lean_inc(v_size_697_);
lean_dec(v_m_694_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_741_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; uint64_t v___x_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v_fold_706_; uint64_t v___x_707_; uint64_t v___x_708_; uint64_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; size_t v___x_714_; lean_object* v_bkt_715_; uint8_t v___x_716_; 
v___x_702_ = lean_array_get_size(v_buckets_698_);
v___x_703_ = l_Lean_Syntax_instHashableRange_hash(v_a_695_);
v___x_704_ = 32ULL;
v___x_705_ = lean_uint64_shift_right(v___x_703_, v___x_704_);
v_fold_706_ = lean_uint64_xor(v___x_703_, v___x_705_);
v___x_707_ = 16ULL;
v___x_708_ = lean_uint64_shift_right(v_fold_706_, v___x_707_);
v___x_709_ = lean_uint64_xor(v_fold_706_, v___x_708_);
v___x_710_ = lean_uint64_to_usize(v___x_709_);
v___x_711_ = lean_usize_of_nat(v___x_702_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_sub(v___x_711_, v___x_712_);
v___x_714_ = lean_usize_land(v___x_710_, v___x_713_);
v_bkt_715_ = lean_array_uget_borrowed(v_buckets_698_, v___x_714_);
v___x_716_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_695_, v_bkt_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v_size_x27_718_; lean_object* v___x_719_; lean_object* v_buckets_x27_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_717_ = lean_unsigned_to_nat(1u);
v_size_x27_718_ = lean_nat_add(v_size_697_, v___x_717_);
lean_dec(v_size_697_);
lean_inc(v_bkt_715_);
v___x_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_719_, 0, v_a_695_);
lean_ctor_set(v___x_719_, 1, v_b_696_);
lean_ctor_set(v___x_719_, 2, v_bkt_715_);
v_buckets_x27_720_ = lean_array_uset(v_buckets_698_, v___x_714_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_mul(v_size_x27_718_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = lean_nat_div(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_array_get_size(v_buckets_x27_720_);
v___x_726_ = lean_nat_dec_le(v___x_724_, v___x_725_);
lean_dec(v___x_724_);
if (v___x_726_ == 0)
{
lean_object* v_val_727_; lean_object* v___x_729_; 
v_val_727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_720_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_val_727_);
lean_ctor_set(v___x_700_, 0, v_size_x27_718_);
v___x_729_ = v___x_700_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_size_x27_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_val_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_732_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_buckets_x27_720_);
lean_ctor_set(v___x_700_, 0, v_size_x27_718_);
v___x_732_ = v___x_700_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_size_x27_718_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_buckets_x27_720_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
lean_object* v___x_734_; lean_object* v_buckets_x27_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
lean_inc(v_bkt_715_);
v___x_734_ = lean_box(0);
v_buckets_x27_735_ = lean_array_uset(v_buckets_698_, v___x_714_, v___x_734_);
v___x_736_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_695_, v_b_696_, v_bkt_715_);
v___x_737_ = lean_array_uset(v_buckets_x27_735_, v___x_714_, v___x_736_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_737_);
v___x_739_ = v___x_700_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_size_697_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_742_, lean_object* v_val_743_, lean_object* v_info_744_, lean_object* v___x_745_, lean_object* v_val_746_, uint8_t v___x_747_, lean_object* v_as_x27_748_, lean_object* v_b_749_, lean_object* v___y_750_){
_start:
{
if (lean_obj_tag(v_as_x27_748_) == 0)
{
lean_object* v___x_752_; 
lean_dec_ref(v_val_746_);
lean_dec(v___x_745_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v_b_749_);
return v___x_752_;
}
else
{
lean_object* v_head_753_; lean_object* v_tail_754_; lean_object* v___x_755_; lean_object* v_env_756_; lean_object* v___x_757_; lean_object* v___x_770_; 
v_head_753_ = lean_ctor_get(v_as_x27_748_, 0);
v_tail_754_ = lean_ctor_get(v_as_x27_748_, 1);
v___x_755_ = lean_st_ref_get(v___y_750_);
v_env_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc_ref(v_env_756_);
lean_dec(v___x_755_);
v___x_757_ = lean_box(0);
lean_inc(v_head_753_);
v___x_770_ = l_Lean_Environment_find_x3f(v_env_756_, v_head_753_, v___x_747_);
if (lean_obj_tag(v___x_770_) == 1)
{
lean_object* v_val_771_; 
v_val_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_771_);
lean_dec_ref_known(v___x_770_, 1);
if (lean_obj_tag(v_val_771_) == 6)
{
lean_object* v_val_772_; lean_object* v_numFields_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_val_772_ = lean_ctor_get(v_val_771_, 0);
lean_inc_ref(v_val_772_);
lean_dec_ref_known(v_val_771_, 1);
v_numFields_773_ = lean_ctor_get(v_val_772_, 4);
lean_inc(v_numFields_773_);
lean_dec_ref(v_val_772_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_nat_dec_lt(v___x_774_, v_numFields_773_);
lean_dec(v_numFields_773_);
if (v___x_775_ == 0)
{
goto v___jp_758_;
}
else
{
v_as_x27_748_ = v_tail_754_;
v_b_749_ = v___x_757_;
goto _start;
}
}
else
{
lean_dec(v_val_771_);
goto v___jp_758_;
}
}
else
{
lean_dec(v___x_770_);
goto v___jp_758_;
}
v___jp_758_:
{
if (lean_obj_tag(v_head_753_) == 1)
{
lean_object* v_str_759_; uint8_t v___x_760_; 
v_str_759_ = lean_ctor_get(v_head_753_, 1);
v___x_760_ = lean_string_dec_eq(v_str_759_, v_str_742_);
if (v___x_760_ == 0)
{
v_as_x27_748_ = v_tail_754_;
v_b_749_ = v___x_757_;
goto _start;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_762_ = lean_st_ref_take(v_val_743_);
v___x_763_ = l_Lean_Elab_Info_stx(v_info_744_);
lean_inc_ref(v_head_753_);
lean_inc(v___x_745_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_745_);
lean_ctor_set(v___x_764_, 1, v_head_753_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_inc_ref(v_val_746_);
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_762_, v_val_746_, v___x_765_);
v___x_767_ = lean_st_ref_set(v_val_743_, v___x_766_);
v_as_x27_748_ = v_tail_754_;
v_b_749_ = v___x_757_;
goto _start;
}
}
else
{
v_as_x27_748_ = v_tail_754_;
v_b_749_ = v___x_757_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_777_, lean_object* v_val_778_, lean_object* v_info_779_, lean_object* v___x_780_, lean_object* v_val_781_, lean_object* v___x_782_, lean_object* v_as_x27_783_, lean_object* v_b_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
uint8_t v___x_22611__boxed_787_; lean_object* v_res_788_; 
v___x_22611__boxed_787_ = lean_unbox(v___x_782_);
v_res_788_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_777_, v_val_778_, v_info_779_, v___x_780_, v_val_781_, v___x_22611__boxed_787_, v_as_x27_783_, v_b_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec(v_as_x27_783_);
lean_dec_ref(v_info_779_);
lean_dec(v_val_778_);
lean_dec_ref(v_str_777_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_789_, v___y_791_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v___x_797_ = lean_whnf(v_a_796_, v___y_790_, v___y_791_, v___y_792_, v___y_793_);
return v___x_797_;
}
else
{
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_805_, lean_object* v___x_806_, lean_object* v_val_807_, lean_object* v___x_808_, lean_object* v_ci_809_, lean_object* v_info_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
if (lean_obj_tag(v_info_810_) == 1)
{
lean_object* v_i_815_; lean_object* v_expr_816_; 
v_i_815_ = lean_ctor_get(v_info_810_, 0);
v_expr_816_ = lean_ctor_get(v_i_815_, 3);
if (lean_obj_tag(v_expr_816_) == 1)
{
lean_object* v_lctx_817_; lean_object* v_expectedType_x3f_818_; uint8_t v_isBinder_819_; lean_object* v_fvarId_820_; lean_object* v___x_821_; 
v_lctx_817_ = lean_ctor_get(v_i_815_, 1);
v_expectedType_x3f_818_ = lean_ctor_get(v_i_815_, 2);
v_isBinder_819_ = lean_ctor_get_uint8(v_i_815_, sizeof(void*)*4);
v_fvarId_820_ = lean_ctor_get(v_expr_816_, 0);
v___x_821_ = l_Lean_Elab_Info_range_x3f(v_info_810_);
if (lean_obj_tag(v___x_821_) == 1)
{
lean_object* v_val_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_977_; 
v_val_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_977_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_977_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_val_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_977_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_826_ = lean_st_ref_get(v_val_805_);
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_826_, v_val_822_);
lean_dec(v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = l_Lean_Elab_Info_stx(v_info_810_);
v___x_829_ = l_Lean_Syntax_getHeadInfo(v___x_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_dec_ref_known(v___x_829_, 4);
if (v_isBinder_819_ == 0)
{
lean_object* v___x_831_; 
lean_dec(v___x_828_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_806_);
v___x_831_ = v___x_824_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_806_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v___x_833_; 
lean_inc(v_fvarId_820_);
lean_inc_ref(v_lctx_817_);
v___x_833_ = lean_local_ctx_find(v_lctx_817_, v_fvarId_820_);
if (lean_obj_tag(v___x_833_) == 1)
{
lean_object* v_val_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_967_; 
v_val_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_967_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_967_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_val_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_967_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_start_838_; uint8_t v___x_839_; 
v_start_838_ = lean_ctor_get(v_val_822_, 0);
v___x_839_ = l_Lean_Syntax_Range_contains(v_val_807_, v_start_838_, v___x_827_);
if (v___x_839_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_val_834_);
lean_dec(v___x_828_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_806_);
v___x_841_ = v___x_836_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_806_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
if (v___x_827_ == 0)
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = l_Lean_LocalDecl_userName(v_val_834_);
lean_dec(v_val_834_);
v___x_844_ = l_Lean_Name_hasMacroScopes(v___x_843_);
lean_dec(v___x_843_);
if (v___x_844_ == 0)
{
lean_object* v_toCommandContextInfo_845_; lean_object* v_options_846_; lean_object* v___x_847_; 
v_toCommandContextInfo_845_ = lean_ctor_get(v_ci_809_, 0);
v_options_846_ = lean_ctor_get(v_toCommandContextInfo_845_, 4);
lean_inc_ref(v_options_846_);
v___x_847_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_846_, v___y_813_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_952_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_952_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_952_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_952_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = l_Lean_Linter_getLinterValue(v___x_808_, v_a_848_);
lean_dec(v_a_848_);
if (v___x_852_ == 0)
{
lean_object* v___x_854_; 
lean_del_object(v___x_836_);
lean_dec(v___x_828_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_806_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_806_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
else
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Syntax_getId(v___x_828_);
lean_dec(v___x_828_);
if (lean_obj_tag(v___x_856_) == 1)
{
lean_object* v_pre_857_; lean_object* v_str_858_; lean_object* v_ty_860_; lean_object* v___y_861_; lean_object* v___y_862_; 
v_pre_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_pre_857_);
v_str_858_ = lean_ctor_get(v___x_856_, 1);
lean_inc_ref(v_str_858_);
if (lean_obj_tag(v_pre_857_) == 0)
{
lean_del_object(v___x_850_);
if (lean_obj_tag(v_expectedType_x3f_818_) == 1)
{
lean_object* v_val_919_; 
lean_del_object(v___x_824_);
v_val_919_ = lean_ctor_get(v_expectedType_x3f_818_, 0);
lean_inc(v_val_919_);
v_ty_860_ = v_val_919_;
v___y_861_ = v___y_812_;
v___y_862_ = v___y_813_;
goto v___jp_859_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_inc_ref(v_expr_816_);
v___x_920_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_920_, 0, v_expr_816_);
lean_inc_ref(v_ci_809_);
lean_inc_ref(v_i_815_);
v___x_921_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_815_, v_ci_809_, v___x_920_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; 
lean_del_object(v___x_824_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v_ty_860_ = v_a_922_;
v___y_861_ = v___y_812_;
v___y_862_ = v___y_813_;
goto v___jp_859_;
}
else
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_943_; 
lean_dec_ref(v_str_858_);
lean_dec_ref_known(v___x_856_, 2);
lean_del_object(v___x_836_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
v_isSharedCheck_943_ = !lean_is_exclusive(v_val_822_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; lean_object* v_unused_945_; 
v_unused_944_ = lean_ctor_get(v_val_822_, 1);
lean_dec(v_unused_944_);
v_unused_945_ = lean_ctor_get(v_val_822_, 0);
lean_dec(v_unused_945_);
v___x_924_ = v_val_822_;
v_isShared_925_ = v_isSharedCheck_943_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_val_822_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_943_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_942_; 
v_a_926_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_942_ == 0)
{
v___x_928_ = v___x_921_;
v_isShared_929_ = v_isSharedCheck_942_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_942_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_ref_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v_ref_930_ = lean_ctor_get(v___y_812_, 7);
v___x_931_ = lean_io_error_to_string(v_a_926_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 3);
lean_ctor_set(v___x_824_, 0, v___x_931_);
v___x_933_ = v___x_824_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_941_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = l_Lean_MessageData_ofFormat(v___x_933_);
lean_inc(v_ref_930_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_934_);
lean_ctor_set(v___x_924_, 0, v_ref_930_);
v___x_936_ = v___x_924_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_ref_930_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v___x_934_);
v___x_936_ = v_reuseFailAlloc_940_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v___x_938_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_936_);
v___x_938_ = v___x_928_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
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
}
}
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v_str_858_);
lean_dec_ref_known(v___x_856_, 2);
lean_dec(v_pre_857_);
lean_del_object(v___x_836_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_806_);
v___x_947_ = v___x_850_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_806_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
v___jp_859_:
{
lean_object* v___f_863_; lean_object* v___x_864_; 
v___f_863_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_863_, 0, v_ty_860_);
lean_inc_ref(v_i_815_);
v___x_864_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_815_, v_ci_809_, v___f_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_895_; 
lean_del_object(v___x_836_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_895_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_895_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_895_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Expr_getAppFn_x27(v_a_865_);
lean_dec(v_a_865_);
if (lean_obj_tag(v___x_869_) == 4)
{
lean_object* v_declName_870_; lean_object* v___x_871_; lean_object* v_env_872_; lean_object* v___x_873_; 
v_declName_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_declName_870_);
lean_dec_ref_known(v___x_869_, 2);
v___x_871_ = lean_st_ref_get(v___y_862_);
v_env_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc_ref(v_env_872_);
lean_dec(v___x_871_);
v___x_873_ = l_Lean_Environment_find_x3f(v_env_872_, v_declName_870_, v___x_827_);
if (lean_obj_tag(v___x_873_) == 1)
{
lean_object* v_val_874_; 
v_val_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v___x_873_, 1);
if (lean_obj_tag(v_val_874_) == 5)
{
lean_object* v_val_875_; lean_object* v_ctors_876_; lean_object* v___x_877_; 
lean_del_object(v___x_867_);
v_val_875_ = lean_ctor_get(v_val_874_, 0);
lean_inc_ref(v_val_875_);
lean_dec_ref_known(v_val_874_, 1);
v_ctors_876_ = lean_ctor_get(v_val_875_, 4);
lean_inc(v_ctors_876_);
lean_dec_ref(v_val_875_);
v___x_877_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_858_, v_val_805_, v_info_810_, v___x_856_, v_val_822_, v___x_827_, v_ctors_876_, v___x_806_, v___y_862_);
lean_dec(v_ctors_876_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_str_858_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_885_);
v___x_879_ = v___x_877_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_dec(v___x_877_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_806_);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_806_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
return v___x_877_;
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v_val_874_);
lean_dec_ref(v_str_858_);
lean_dec_ref_known(v___x_856_, 2);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_806_);
v___x_887_ = v___x_867_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_806_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v___x_890_; 
lean_dec(v___x_873_);
lean_dec_ref(v_str_858_);
lean_dec_ref_known(v___x_856_, 2);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_806_);
v___x_890_ = v___x_867_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_806_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
else
{
lean_object* v___x_893_; 
lean_dec_ref(v___x_869_);
lean_dec_ref(v_str_858_);
lean_dec_ref_known(v___x_856_, 2);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_806_);
v___x_893_ = v___x_867_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_806_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_str_858_);
lean_dec_ref_known(v___x_856_, 2);
lean_dec_ref_known(v_info_810_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_val_822_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; lean_object* v_unused_918_; 
v_unused_917_ = lean_ctor_get(v_val_822_, 1);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_val_822_, 0);
lean_dec(v_unused_918_);
v___x_897_ = v_val_822_;
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_val_822_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_915_; 
v_a_899_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_915_ == 0)
{
v___x_901_ = v___x_864_;
v_isShared_902_ = v_isSharedCheck_915_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_864_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_915_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_ref_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
v_ref_903_ = lean_ctor_get(v___y_861_, 7);
v___x_904_ = lean_io_error_to_string(v_a_899_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 3);
lean_ctor_set(v___x_836_, 0, v___x_904_);
v___x_906_ = v___x_836_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_914_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = l_Lean_MessageData_ofFormat(v___x_906_);
lean_inc(v_ref_903_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_907_);
lean_ctor_set(v___x_897_, 0, v_ref_903_);
v___x_909_ = v___x_897_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_ref_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_913_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
lean_object* v___x_911_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_909_);
v___x_911_ = v___x_901_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
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
lean_object* v___x_950_; 
lean_dec(v___x_856_);
lean_del_object(v___x_836_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_806_);
v___x_950_ = v___x_850_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_806_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_del_object(v___x_836_);
lean_dec(v___x_828_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
v_a_953_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_847_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_847_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
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
lean_object* v___x_962_; 
lean_dec(v___x_828_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_806_);
v___x_962_ = v___x_836_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_806_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
else
{
lean_object* v___x_965_; 
lean_dec(v_val_834_);
lean_dec(v___x_828_);
lean_del_object(v___x_824_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_806_);
v___x_965_ = v___x_836_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_806_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
else
{
lean_object* v___x_969_; 
lean_dec(v___x_833_);
lean_dec(v___x_828_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_806_);
v___x_969_ = v___x_824_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_806_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
else
{
lean_object* v___x_972_; 
lean_dec(v___x_829_);
lean_dec(v___x_828_);
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_806_);
v___x_972_ = v___x_824_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_806_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_object* v___x_975_; 
lean_dec(v_val_822_);
lean_dec_ref_known(v_info_810_, 1);
lean_dec_ref(v_ci_809_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 0);
lean_ctor_set(v___x_824_, 0, v___x_806_);
v___x_975_ = v___x_824_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_806_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v___x_821_);
lean_dec_ref(v_ci_809_);
v_isSharedCheck_984_ = !lean_is_exclusive(v_info_810_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; 
v_unused_985_ = lean_ctor_get(v_info_810_, 0);
lean_dec(v_unused_985_);
v___x_979_ = v_info_810_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_dec(v_info_810_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set_tag(v___x_979_, 0);
lean_ctor_set(v___x_979_, 0, v___x_806_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_806_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_ci_809_);
v_isSharedCheck_992_ = !lean_is_exclusive(v_info_810_);
if (v_isSharedCheck_992_ == 0)
{
lean_object* v_unused_993_; 
v_unused_993_ = lean_ctor_get(v_info_810_, 0);
lean_dec(v_unused_993_);
v___x_987_ = v_info_810_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_dec(v_info_810_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v___x_806_);
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_806_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v___x_994_; 
lean_dec_ref(v_info_810_);
lean_dec_ref(v_ci_809_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_806_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_995_, lean_object* v___x_996_, lean_object* v_val_997_, lean_object* v___x_998_, lean_object* v_ci_999_, lean_object* v_info_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_995_, v___x_996_, v_val_997_, v___x_998_, v_ci_999_, v_info_1000_, v_x_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec_ref(v_x_1001_);
lean_dec_ref(v___x_998_);
lean_dec_ref(v_val_997_);
lean_dec(v_val_995_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_1006_, lean_object* v_ci_1007_, lean_object* v_i_1008_, lean_object* v_cs_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1014_; 
lean_inc(v___y_1012_);
lean_inc_ref(v___y_1011_);
v___x_1014_ = lean_apply_6(v_postNode_1006_, v_ci_1007_, v_i_1008_, v_cs_1009_, v___y_1011_, v___y_1012_, lean_box(0));
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1015_, lean_object* v_ci_1016_, lean_object* v_i_1017_, lean_object* v_cs_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1015_, v_ci_1016_, v_i_1017_, v_cs_1018_, v_x_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v_x_1019_);
return v_res_1023_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_instMonadEIO(lean_box(0));
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v_toApplicative_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1064_; 
v___x_1031_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1032_ = l_StateRefT_x27_instMonad___redArg(v___x_1031_);
v_toApplicative_1033_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1032_, 1);
lean_dec(v_unused_1065_);
v___x_1035_ = v___x_1032_;
v_isShared_1036_ = v_isSharedCheck_1064_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_toApplicative_1033_);
lean_dec(v___x_1032_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1064_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_toFunctor_1037_; lean_object* v_toSeq_1038_; lean_object* v_toSeqLeft_1039_; lean_object* v_toSeqRight_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1062_; 
v_toFunctor_1037_ = lean_ctor_get(v_toApplicative_1033_, 0);
v_toSeq_1038_ = lean_ctor_get(v_toApplicative_1033_, 2);
v_toSeqLeft_1039_ = lean_ctor_get(v_toApplicative_1033_, 3);
v_toSeqRight_1040_ = lean_ctor_get(v_toApplicative_1033_, 4);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_toApplicative_1033_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_toApplicative_1033_, 1);
lean_dec(v_unused_1063_);
v___x_1042_ = v_toApplicative_1033_;
v_isShared_1043_ = v_isSharedCheck_1062_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_toSeqRight_1040_);
lean_inc(v_toSeqLeft_1039_);
lean_inc(v_toSeq_1038_);
lean_inc(v_toFunctor_1037_);
lean_dec(v_toApplicative_1033_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1062_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1053_; 
v___f_1044_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1045_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1037_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toFunctor_1037_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toFunctor_1037_);
v___x_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___f_1046_);
lean_ctor_set(v___x_1048_, 1, v___f_1047_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeqRight_1040_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toSeqLeft_1039_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toSeq_1038_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___f_1049_);
lean_ctor_set(v___x_1042_, 3, v___f_1050_);
lean_ctor_set(v___x_1042_, 2, v___f_1051_);
lean_ctor_set(v___x_1042_, 1, v___f_1044_);
lean_ctor_set(v___x_1042_, 0, v___x_1048_);
v___x_1053_ = v___x_1042_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___f_1044_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v___f_1051_);
lean_ctor_set(v_reuseFailAlloc_1061_, 3, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1061_, 4, v___f_1049_);
v___x_1053_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___f_1045_);
lean_ctor_set(v___x_1035_, 0, v___x_1053_);
v___x_1055_ = v___x_1035_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___f_1045_);
v___x_1055_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_18819__overap_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_box(0);
v___x_1057_ = l_instInhabitedOfMonad___redArg(v___x_1055_, v___x_1056_);
v___x_18819__overap_1058_ = lean_panic_fn_borrowed(v___x_1057_, v_msg_1027_);
lean_dec(v___x_1057_);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
v___x_1059_ = lean_apply_3(v___x_18819__overap_1058_, v___y_1028_, v___y_1029_, lean_box(0));
return v___x_1059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1070_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1075_ = lean_unsigned_to_nat(21u);
v___x_1076_ = lean_unsigned_to_nat(65u);
v___x_1077_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1078_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1079_ = l_mkPanicMessageWithDecl(v___x_1078_, v___x_1077_, v___x_1076_, v___x_1075_, v___x_1074_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1080_, lean_object* v_postNode_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
switch(lean_obj_tag(v_x_1083_))
{
case 0:
{
lean_object* v_i_1087_; lean_object* v_t_1088_; lean_object* v___x_1089_; 
v_i_1087_ = lean_ctor_get(v_x_1083_, 0);
lean_inc_ref(v_i_1087_);
v_t_1088_ = lean_ctor_get(v_x_1083_, 1);
lean_inc_ref(v_t_1088_);
lean_dec_ref_known(v_x_1083_, 2);
v___x_1089_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1087_, v_x_1082_);
v_x_1082_ = v___x_1089_;
v_x_1083_ = v_t_1088_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1082_) == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref_known(v_x_1083_, 2);
lean_dec_ref(v_postNode_1081_);
lean_dec_ref(v_preNode_1080_);
v___x_1091_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1092_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1091_, v___y_1084_, v___y_1085_);
return v___x_1092_;
}
else
{
lean_object* v_i_1093_; lean_object* v_children_1094_; lean_object* v_val_1095_; lean_object* v___x_1096_; 
v_i_1093_ = lean_ctor_get(v_x_1083_, 0);
lean_inc_ref_n(v_i_1093_, 2);
v_children_1094_ = lean_ctor_get(v_x_1083_, 1);
lean_inc_ref_n(v_children_1094_, 2);
lean_dec_ref_known(v_x_1083_, 2);
v_val_1095_ = lean_ctor_get(v_x_1082_, 0);
lean_inc_n(v_val_1095_, 2);
lean_inc_ref(v_preNode_1080_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
v___x_1096_ = lean_apply_6(v_preNode_1080_, v_val_1095_, v_i_1093_, v_children_1094_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; uint8_t v___x_1098_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_unbox(v_a_1097_);
lean_dec(v_a_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_preNode_1080_);
v_isSharedCheck_1123_ = !lean_is_exclusive(v_x_1082_);
if (v_isSharedCheck_1123_ == 0)
{
lean_object* v_unused_1124_; 
v_unused_1124_ = lean_ctor_get(v_x_1082_, 0);
lean_dec(v_unused_1124_);
v___x_1100_ = v_x_1082_;
v_isShared_1101_ = v_isSharedCheck_1123_;
goto v_resetjp_1099_;
}
else
{
lean_dec(v_x_1082_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1123_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_box(0);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
v___x_1103_ = lean_apply_7(v_postNode_1081_, v_val_1095_, v_i_1093_, v_children_1094_, v___x_1102_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_a_1104_);
v___x_1109_ = v___x_1100_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_del_object(v___x_1100_);
v_a_1115_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1103_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1103_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1125_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1082_, v_i_1093_);
v___x_1126_ = l_Lean_PersistentArray_toList___redArg(v_children_1094_);
v___x_1127_ = lean_box(0);
lean_inc_ref(v_postNode_1081_);
v___x_1128_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1080_, v_postNode_1081_, v___x_1125_, v___x_1126_, v___x_1127_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
v___x_1130_ = lean_apply_7(v_postNode_1081_, v_val_1095_, v_i_1093_, v_children_1094_, v_a_1129_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v_a_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
v_a_1140_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1130_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1130_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v_val_1095_);
lean_dec_ref(v_children_1094_);
lean_dec_ref(v_i_1093_);
lean_dec_ref(v_postNode_1081_);
v_a_1148_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1128_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1128_);
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
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_val_1095_);
lean_dec_ref(v_children_1094_);
lean_dec_ref(v_i_1093_);
lean_dec_ref_known(v_x_1082_, 1);
lean_dec_ref(v_postNode_1081_);
lean_dec_ref(v_preNode_1080_);
v_a_1156_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1096_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1096_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
default: 
{
lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_x_1082_);
lean_dec_ref(v_postNode_1081_);
lean_dec_ref(v_preNode_1080_);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_x_1083_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v_x_1083_, 0);
lean_dec(v_unused_1172_);
v___x_1165_ = v_x_1083_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_dec(v_x_1083_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_box(0);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1173_, lean_object* v_postNode_1174_, lean_object* v___x_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec(v___x_1175_);
lean_dec_ref(v_postNode_1174_);
lean_dec_ref(v_preNode_1173_);
v___x_1181_ = l_List_reverse___redArg(v_x_1177_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
else
{
lean_object* v_head_1183_; lean_object* v_tail_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1202_; 
v_head_1183_ = lean_ctor_get(v_x_1176_, 0);
v_tail_1184_ = lean_ctor_get(v_x_1176_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1186_ = v_x_1176_;
v_isShared_1187_ = v_isSharedCheck_1202_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_tail_1184_);
lean_inc(v_head_1183_);
lean_dec(v_x_1176_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1202_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; 
lean_inc(v___x_1175_);
lean_inc_ref(v_postNode_1174_);
lean_inc_ref(v_preNode_1173_);
v___x_1188_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1173_, v_postNode_1174_, v___x_1175_, v_head_1183_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v_x_1177_);
lean_ctor_set(v___x_1186_, 0, v_a_1189_);
v___x_1191_ = v___x_1186_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1189_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_x_1177_);
v___x_1191_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
v_x_1176_ = v_tail_1184_;
v_x_1177_ = v___x_1191_;
goto _start;
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_del_object(v___x_1186_);
lean_dec(v_tail_1184_);
lean_dec(v_x_1177_);
lean_dec(v___x_1175_);
lean_dec_ref(v_postNode_1174_);
lean_dec_ref(v_preNode_1173_);
v_a_1194_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1188_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1188_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1203_, lean_object* v_postNode_1204_, lean_object* v___x_1205_, lean_object* v_x_1206_, lean_object* v_x_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1203_, v_postNode_1204_, v___x_1205_, v_x_1206_, v_x_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1212_, lean_object* v_postNode_1213_, lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1212_, v_postNode_1213_, v_x_1214_, v_x_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1220_, lean_object* v_postNode_1221_, lean_object* v_ctx_x3f_1222_, lean_object* v_t_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___f_1227_; lean_object* v___x_1228_; 
v___f_1227_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1227_, 0, v_postNode_1221_);
v___x_1228_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1220_, v___f_1227_, v_ctx_x3f_1222_, v_t_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1236_; 
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; 
v_unused_1237_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1237_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1236_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(0);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1234_ = v___x_1230_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
v_a_1238_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1228_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1228_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1246_, lean_object* v_postNode_1247_, lean_object* v_ctx_x3f_1248_, lean_object* v_t_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1246_, v_postNode_1247_, v_ctx_x3f_1248_, v_t_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1254_, lean_object* v_val_1255_, lean_object* v_val_1256_, lean_object* v_as_1257_, size_t v_sz_1258_, size_t v_i_1259_, lean_object* v_b_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_usize_dec_lt(v_i_1259_, v_sz_1258_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref(v_val_1256_);
lean_dec(v_val_1255_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_b_1260_);
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1266_ = lean_box(v___x_1254_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1267_, 0, v___x_1266_);
v___x_1268_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1269_ = lean_box(0);
lean_inc_ref(v_val_1256_);
lean_inc(v_val_1255_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1270_, 0, v_val_1255_);
lean_closure_set(v___f_1270_, 1, v___x_1269_);
lean_closure_set(v___f_1270_, 2, v_val_1256_);
lean_closure_set(v___f_1270_, 3, v___x_1268_);
v_a_1271_ = lean_array_uget_borrowed(v_as_1257_, v_i_1259_);
v___x_1272_ = lean_box(0);
lean_inc(v_a_1271_);
v___x_1273_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1267_, v___f_1270_, v___x_1272_, v_a_1271_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1273_) == 0)
{
size_t v___x_1274_; size_t v___x_1275_; 
lean_dec_ref_known(v___x_1273_, 1);
v___x_1274_ = ((size_t)1ULL);
v___x_1275_ = lean_usize_add(v_i_1259_, v___x_1274_);
v_i_1259_ = v___x_1275_;
v_b_1260_ = v___x_1269_;
goto _start;
}
else
{
lean_dec_ref(v_val_1256_);
lean_dec(v_val_1255_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1277_, lean_object* v_val_1278_, lean_object* v_val_1279_, lean_object* v_as_1280_, lean_object* v_sz_1281_, lean_object* v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
uint8_t v___x_23475__boxed_1287_; size_t v_sz_boxed_1288_; size_t v_i_boxed_1289_; lean_object* v_res_1290_; 
v___x_23475__boxed_1287_ = lean_unbox(v___x_1277_);
v_sz_boxed_1288_ = lean_unbox_usize(v_sz_1281_);
lean_dec(v_sz_1281_);
v_i_boxed_1289_ = lean_unbox_usize(v_i_1282_);
lean_dec(v_i_1282_);
v_res_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23475__boxed_1287_, v_val_1278_, v_val_1279_, v_as_1280_, v_sz_boxed_1288_, v_i_boxed_1289_, v_b_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_as_1280_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1291_, lean_object* v_x_1292_){
_start:
{
if (lean_obj_tag(v_x_1292_) == 0)
{
return v_x_1291_;
}
else
{
lean_object* v_key_1293_; lean_object* v_value_1294_; lean_object* v_tail_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_key_1293_ = lean_ctor_get(v_x_1292_, 0);
v_value_1294_ = lean_ctor_get(v_x_1292_, 1);
v_tail_1295_ = lean_ctor_get(v_x_1292_, 2);
lean_inc(v_value_1294_);
lean_inc(v_key_1293_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_key_1293_);
lean_ctor_set(v___x_1296_, 1, v_value_1294_);
v___x_1297_ = lean_array_push(v_x_1291_, v___x_1296_);
v_x_1291_ = v___x_1297_;
v_x_1292_ = v_tail_1295_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1299_, v_x_1300_);
lean_dec(v_x_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1302_, size_t v_i_1303_, size_t v_stop_1304_, lean_object* v_b_1305_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_eq(v_i_1303_, v_stop_1304_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1308_; size_t v___x_1309_; size_t v___x_1310_; 
v___x_1307_ = lean_array_uget_borrowed(v_as_1302_, v_i_1303_);
v___x_1308_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1305_, v___x_1307_);
v___x_1309_ = ((size_t)1ULL);
v___x_1310_ = lean_usize_add(v_i_1303_, v___x_1309_);
v_i_1303_ = v___x_1310_;
v_b_1305_ = v___x_1308_;
goto _start;
}
else
{
return v_b_1305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1312_, lean_object* v_i_1313_, lean_object* v_stop_1314_, lean_object* v_b_1315_){
_start:
{
size_t v_i_boxed_1316_; size_t v_stop_boxed_1317_; lean_object* v_res_1318_; 
v_i_boxed_1316_ = lean_unbox_usize(v_i_1313_);
lean_dec(v_i_1313_);
v_stop_boxed_1317_ = lean_unbox_usize(v_stop_1314_);
lean_dec(v_stop_1314_);
v_res_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1312_, v_i_boxed_1316_, v_stop_boxed_1317_, v_b_1315_);
lean_dec_ref(v_as_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v_scopes_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_opts_1326_; lean_object* v___x_1327_; 
v___x_1322_ = lean_st_ref_get(v___y_1320_);
v_scopes_1323_ = lean_ctor_get(v___x_1322_, 2);
lean_inc(v_scopes_1323_);
lean_dec(v___x_1322_);
v___x_1324_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1325_ = l_List_head_x21___redArg(v___x_1324_, v_scopes_1323_);
lean_dec(v_scopes_1323_);
v_opts_1326_ = lean_ctor_get(v___x_1325_, 1);
lean_inc_ref(v_opts_1326_);
lean_dec(v___x_1325_);
v___x_1327_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1326_, v___y_1320_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1331_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_unsigned_to_nat(16u);
v___x_1334_ = lean_mk_array(v___x_1333_, v___x_1332_);
return v___x_1334_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1335_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
lean_ctor_set(v___x_1337_, 1, v___x_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1413_; 
v___x_1342_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1339_, v___y_1340_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1413_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1413_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1348_ = l_Lean_Linter_getLinterValue(v___x_1347_, v_a_1343_);
lean_dec(v_a_1343_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
uint8_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = 0;
v___x_1354_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1338_, v___x_1353_);
if (lean_obj_tag(v___x_1354_) == 1)
{
lean_object* v_val_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v_infoState_1360_; lean_object* v_trees_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; size_t v_sz_1364_; size_t v___x_1365_; lean_object* v___x_1366_; 
lean_del_object(v___x_1345_);
v_val_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = lean_st_ref_get(v___y_1340_);
v___x_1357_ = lean_unsigned_to_nat(0u);
v___x_1358_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1359_ = lean_st_mk_ref(v___x_1358_);
v_infoState_1360_ = lean_ctor_get(v___x_1356_, 8);
lean_inc_ref(v_infoState_1360_);
lean_dec(v___x_1356_);
v_trees_1361_ = lean_ctor_get(v_infoState_1360_, 2);
lean_inc_ref(v_trees_1361_);
lean_dec_ref(v_infoState_1360_);
v___x_1362_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1361_);
lean_dec_ref(v_trees_1361_);
v___x_1363_ = lean_box(0);
v_sz_1364_ = lean_array_size(v___x_1362_);
v___x_1365_ = ((size_t)0ULL);
lean_inc(v___x_1359_);
v___x_1366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1348_, v___x_1359_, v_val_1355_, v___x_1362_, v_sz_1364_, v___x_1365_, v___x_1363_, v___y_1339_, v___y_1340_);
lean_dec_ref(v___x_1362_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; lean_object* v___y_1369_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1393_; lean_object* v_size_1399_; lean_object* v_buckets_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
lean_dec_ref_known(v___x_1366_, 1);
v___x_1367_ = lean_st_ref_get(v___x_1359_);
lean_dec(v___x_1359_);
v_size_1399_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_size_1399_);
v_buckets_1400_ = lean_ctor_get(v___x_1367_, 1);
lean_inc_ref(v_buckets_1400_);
lean_dec(v___x_1367_);
v___x_1401_ = lean_mk_empty_array_with_capacity(v_size_1399_);
lean_dec(v_size_1399_);
v___x_1402_ = lean_array_get_size(v_buckets_1400_);
v___x_1403_ = lean_nat_dec_lt(v___x_1357_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_dec_ref(v_buckets_1400_);
v___y_1393_ = v___x_1401_;
goto v___jp_1392_;
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = lean_nat_dec_le(v___x_1402_, v___x_1402_);
if (v___x_1404_ == 0)
{
if (v___x_1403_ == 0)
{
lean_dec_ref(v_buckets_1400_);
v___y_1393_ = v___x_1401_;
goto v___jp_1392_;
}
else
{
size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_usize_of_nat(v___x_1402_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1400_, v___x_1365_, v___x_1405_, v___x_1401_);
lean_dec_ref(v_buckets_1400_);
v___y_1393_ = v___x_1406_;
goto v___jp_1392_;
}
}
else
{
size_t v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_usize_of_nat(v___x_1402_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1400_, v___x_1365_, v___x_1407_, v___x_1401_);
lean_dec_ref(v_buckets_1400_);
v___y_1393_ = v___x_1408_;
goto v___jp_1392_;
}
}
v___jp_1368_:
{
size_t v_sz_1370_; lean_object* v___x_1371_; 
v_sz_1370_ = lean_array_size(v___y_1369_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1369_, v_sz_1370_, v___x_1365_, v___x_1363_, v___y_1339_, v___y_1340_);
lean_dec_ref(v___y_1369_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1371_, 0);
lean_dec(v_unused_1379_);
v___x_1373_ = v___x_1371_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v___x_1371_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1363_);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1363_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
return v___x_1371_;
}
}
v___jp_1380_:
{
lean_object* v___x_1385_; 
v___x_1385_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1382_, v___y_1381_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec(v___y_1382_);
v___y_1369_ = v___x_1385_;
goto v___jp_1368_;
}
v___jp_1386_:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_nat_dec_le(v___y_1390_, v___y_1388_);
if (v___x_1391_ == 0)
{
lean_dec(v___y_1388_);
lean_inc(v___y_1390_);
v___y_1381_ = v___y_1387_;
v___y_1382_ = v___y_1389_;
v___y_1383_ = v___y_1390_;
v___y_1384_ = v___y_1390_;
goto v___jp_1380_;
}
else
{
v___y_1381_ = v___y_1387_;
v___y_1382_ = v___y_1389_;
v___y_1383_ = v___y_1390_;
v___y_1384_ = v___y_1388_;
goto v___jp_1380_;
}
}
v___jp_1392_:
{
lean_object* v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = lean_array_get_size(v___y_1393_);
v___x_1395_ = lean_nat_dec_eq(v___x_1394_, v___x_1357_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1396_ = lean_unsigned_to_nat(1u);
v___x_1397_ = lean_nat_sub(v___x_1394_, v___x_1396_);
v___x_1398_ = lean_nat_dec_le(v___x_1357_, v___x_1397_);
if (v___x_1398_ == 0)
{
lean_inc(v___x_1397_);
v___y_1387_ = v___y_1393_;
v___y_1388_ = v___x_1397_;
v___y_1389_ = v___x_1394_;
v___y_1390_ = v___x_1397_;
goto v___jp_1386_;
}
else
{
v___y_1387_ = v___y_1393_;
v___y_1388_ = v___x_1397_;
v___y_1389_ = v___x_1394_;
v___y_1390_ = v___x_1357_;
goto v___jp_1386_;
}
}
else
{
v___y_1369_ = v___y_1393_;
goto v___jp_1368_;
}
}
}
else
{
lean_dec(v___x_1359_);
return v___x_1366_;
}
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_dec(v___x_1354_);
v___x_1409_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1409_);
v___x_1411_ = v___x_1345_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v_cmdStx_1414_);
return v_res_1418_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1428_, lean_object* v_m_1429_, lean_object* v_a_1430_){
_start:
{
uint8_t v___x_1431_; 
v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1429_, v_a_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1432_, lean_object* v_m_1433_, lean_object* v_a_1434_){
_start:
{
uint8_t v_res_1435_; lean_object* v_r_1436_; 
v_res_1435_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1432_, v_m_1433_, v_a_1434_);
lean_dec_ref(v_a_1434_);
lean_dec_ref(v_m_1433_);
v_r_1436_ = lean_box(v_res_1435_);
return v_r_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1437_, lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1438_, v_a_1439_, v_b_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1442_, lean_object* v_val_1443_, lean_object* v_info_1444_, lean_object* v___x_1445_, lean_object* v_val_1446_, uint8_t v___x_1447_, lean_object* v_as_1448_, lean_object* v_as_x27_1449_, lean_object* v_b_1450_, lean_object* v_a_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1442_, v_val_1443_, v_info_1444_, v___x_1445_, v_val_1446_, v___x_1447_, v_as_x27_1449_, v_b_1450_, v___y_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1456_, lean_object* v_val_1457_, lean_object* v_info_1458_, lean_object* v___x_1459_, lean_object* v_val_1460_, lean_object* v___x_1461_, lean_object* v_as_1462_, lean_object* v_as_x27_1463_, lean_object* v_b_1464_, lean_object* v_a_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
uint8_t v___x_23767__boxed_1469_; lean_object* v_res_1470_; 
v___x_23767__boxed_1469_ = lean_unbox(v___x_1461_);
v_res_1470_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1456_, v_val_1457_, v_info_1458_, v___x_1459_, v_val_1460_, v___x_23767__boxed_1469_, v_as_1462_, v_as_x27_1463_, v_b_1464_, v_a_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v_as_x27_1463_);
lean_dec(v_as_1462_);
lean_dec_ref(v_info_1458_);
lean_dec(v_val_1457_);
lean_dec_ref(v_str_1456_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1471_, lean_object* v_as_1472_, lean_object* v_lo_1473_, lean_object* v_hi_1474_, lean_object* v_w_1475_, lean_object* v_hlo_1476_, lean_object* v_hhi_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1471_, v_as_1472_, v_lo_1473_, v_hi_1474_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1479_, lean_object* v_as_1480_, lean_object* v_lo_1481_, lean_object* v_hi_1482_, lean_object* v_w_1483_, lean_object* v_hlo_1484_, lean_object* v_hhi_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1479_, v_as_1480_, v_lo_1481_, v_hi_1482_, v_w_1483_, v_hlo_1484_, v_hhi_1485_);
lean_dec(v_hi_1482_);
lean_dec(v_n_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1487_, lean_object* v_a_1488_, lean_object* v_x_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1488_, v_x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1491_, lean_object* v_a_1492_, lean_object* v_x_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1491_, v_a_1492_, v_x_1493_);
lean_dec(v_x_1493_);
lean_dec_ref(v_a_1492_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1496_, lean_object* v_data_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1499_, lean_object* v_a_1500_, lean_object* v_b_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1500_, v_b_1501_, v_x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1504_, lean_object* v_msg_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1510_, v_msg_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1516_, lean_object* v_preNode_1517_, lean_object* v_postNode_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1517_, v_postNode_1518_, v_x_1519_, v_x_1520_, v___y_1521_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1525_, lean_object* v_preNode_1526_, lean_object* v_postNode_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1525_, v_preNode_1526_, v_postNode_1527_, v_x_1528_, v_x_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object* v_n_1534_, lean_object* v_lo_1535_, lean_object* v_hi_1536_, lean_object* v_hhi_1537_, lean_object* v_pivot_1538_, lean_object* v_as_1539_, lean_object* v_i_1540_, lean_object* v_k_1541_, lean_object* v_ilo_1542_, lean_object* v_ik_1543_, lean_object* v_w_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1536_, v_pivot_1538_, v_as_1539_, v_i_1540_, v_k_1541_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object* v_n_1546_, lean_object* v_lo_1547_, lean_object* v_hi_1548_, lean_object* v_hhi_1549_, lean_object* v_pivot_1550_, lean_object* v_as_1551_, lean_object* v_i_1552_, lean_object* v_k_1553_, lean_object* v_ilo_1554_, lean_object* v_ik_1555_, lean_object* v_w_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_1546_, v_lo_1547_, v_hi_1548_, v_hhi_1549_, v_pivot_1550_, v_as_1551_, v_i_1552_, v_k_1553_, v_ilo_1554_, v_ik_1555_, v_w_1556_);
lean_dec_ref(v_pivot_1550_);
lean_dec(v_hi_1548_);
lean_dec(v_lo_1547_);
lean_dec(v_n_1546_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1558_, lean_object* v_i_1559_, lean_object* v_source_1560_, lean_object* v_target_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1559_, v_source_1560_, v_target_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1563_, lean_object* v_preNode_1564_, lean_object* v_postNode_1565_, lean_object* v___x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1564_, v_postNode_1565_, v___x_1566_, v_x_1567_, v_x_1568_, v___y_1569_, v___y_1570_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_preNode_1574_, lean_object* v_postNode_1575_, lean_object* v___x_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1573_, v_preNode_1574_, v_postNode_1575_, v___x_1576_, v_x_1577_, v_x_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1583_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1588_, v___y_1589_, v___y_1590_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1594_, v_x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1599_ = l_Lean_Elab_Command_addLinter(v___x_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1601_;
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
