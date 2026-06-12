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
uint8_t v___y_21708__boxed_227_; uint8_t v_suppressElabErrors_boxed_228_; uint8_t v_res_229_; lean_object* v_r_230_; 
v___y_21708__boxed_227_ = lean_unbox(v___y_224_);
v_suppressElabErrors_boxed_228_ = lean_unbox(v_suppressElabErrors_225_);
v_res_229_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21708__boxed_227_, v_suppressElabErrors_boxed_228_, v_x_226_);
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
lean_object* v___y_292_; uint8_t v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; lean_object* v___y_296_; uint8_t v___y_297_; lean_object* v___y_298_; lean_object* v___y_299_; uint8_t v___y_355_; uint8_t v___y_356_; lean_object* v___y_357_; uint8_t v___y_358_; lean_object* v___y_359_; uint8_t v___y_383_; uint8_t v___y_384_; lean_object* v___y_385_; uint8_t v___y_386_; lean_object* v___y_387_; uint8_t v___y_391_; uint8_t v___y_392_; uint8_t v___y_393_; uint8_t v___x_408_; uint8_t v___y_410_; uint8_t v___y_411_; uint8_t v___y_412_; uint8_t v___y_414_; uint8_t v___x_426_; 
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
lean_ctor_set(v___x_325_, 1, v___y_295_);
lean_inc_ref(v___y_292_);
lean_inc_ref(v___y_298_);
v___x_326_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_326_, 0, v___y_298_);
lean_ctor_set(v___x_326_, 1, v___y_296_);
lean_ctor_set(v___x_326_, 2, v___y_294_);
lean_ctor_set(v___x_326_, 3, v___y_292_);
lean_ctor_set(v___x_326_, 4, v___x_325_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*5, v___y_297_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*5 + 1, v___y_293_);
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
lean_dec_ref(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
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
lean_dec_ref(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
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
v___y_292_ = v___x_372_;
v___y_293_ = v___y_356_;
v___y_294_ = v___x_371_;
v___y_295_ = v_a_365_;
v___y_296_ = v___x_369_;
v___y_297_ = v___y_358_;
v___y_298_ = v_fileName_360_;
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
v___y_292_ = v___x_372_;
v___y_293_ = v___y_356_;
v___y_294_ = v___x_371_;
v___y_295_ = v_a_365_;
v___y_296_ = v___x_369_;
v___y_297_ = v___y_358_;
v___y_298_ = v_fileName_360_;
v___y_299_ = v___y_289_;
goto v___jp_291_;
}
}
}
}
v___jp_382_:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Syntax_getTailPos_x3f(v___y_385_, v___y_386_);
lean_dec(v___y_385_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_inc(v___y_387_);
v___y_355_ = v___y_383_;
v___y_356_ = v___y_384_;
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
v___y_356_ = v___y_384_;
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
v___y_384_ = v___y_393_;
v___y_385_ = v_ref_396_;
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
v___y_384_ = v___y_393_;
v___y_385_ = v_ref_396_;
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
lean_object* v_name_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_481_; 
v_name_464_ = lean_ctor_get(v_linterOption_458_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_linterOption_458_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v_linterOption_458_, 1);
lean_dec(v_unused_482_);
v___x_466_ = v_linterOption_458_;
v_isShared_467_ = v_isSharedCheck_481_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_name_464_);
lean_dec(v_linterOption_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_481_;
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
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_480_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_disable_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
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
v___x_479_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_459_, v___x_478_, v___y_461_, v___y_462_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_483_, lean_object* v_stx_484_, lean_object* v_msg_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_483_, v_stx_484_, v_msg_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v_stx_484_);
return v_res_489_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_504_ = l_Lean_stringToMessageData(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_507_ = l_Lean_stringToMessageData(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_508_, size_t v_sz_509_, size_t v_i_510_, lean_object* v_b_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___x_515_; 
v___x_515_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v_b_511_);
return v___x_516_;
}
else
{
lean_object* v_a_517_; lean_object* v_snd_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_563_; 
v_a_517_ = lean_array_uget(v_as_508_, v_i_510_);
v_snd_518_ = lean_ctor_get(v_a_517_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_a_517_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_a_517_, 0);
lean_dec(v_unused_564_);
v___x_520_ = v_a_517_;
v_isShared_521_ = v_isSharedCheck_563_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_snd_518_);
lean_dec(v_a_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_563_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_snd_522_; lean_object* v_fst_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_562_; 
v_snd_522_ = lean_ctor_get(v_snd_518_, 1);
v_fst_523_ = lean_ctor_get(v_snd_518_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_snd_518_);
if (v_isSharedCheck_562_ == 0)
{
v___x_525_ = v_snd_518_;
v_isShared_526_ = v_isSharedCheck_562_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snd_522_);
lean_inc(v_fst_523_);
lean_dec(v_snd_518_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_562_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_fst_527_; lean_object* v_snd_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_561_; 
v_fst_527_ = lean_ctor_get(v_snd_522_, 0);
v_snd_528_ = lean_ctor_get(v_snd_522_, 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_snd_522_);
if (v_isSharedCheck_561_ == 0)
{
v___x_530_ = v_snd_522_;
v_isShared_531_ = v_isSharedCheck_561_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_snd_528_);
lean_inc(v_fst_527_);
lean_dec(v_snd_522_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_561_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_532_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_534_ = l_Lean_MessageData_ofName(v_fst_527_);
lean_inc_ref(v___x_534_);
if (v_isShared_531_ == 0)
{
lean_ctor_set_tag(v___x_530_, 7);
lean_ctor_set(v___x_530_, 1, v___x_534_);
lean_ctor_set(v___x_530_, 0, v___x_533_);
v___x_536_ = v___x_530_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_534_);
v___x_536_ = v_reuseFailAlloc_560_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_526_ == 0)
{
lean_ctor_set_tag(v___x_525_, 7);
lean_ctor_set(v___x_525_, 1, v___x_537_);
lean_ctor_set(v___x_525_, 0, v___x_536_);
v___x_539_ = v___x_525_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_537_);
v___x_539_ = v_reuseFailAlloc_559_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_540_ = l_Lean_MessageData_ofName(v_snd_528_);
lean_inc_ref(v___x_540_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 7);
lean_ctor_set(v___x_520_, 1, v___x_540_);
lean_ctor_set(v___x_520_, 0, v___x_539_);
v___x_542_ = v___x_520_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_540_);
v___x_542_ = v_reuseFailAlloc_558_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_534_);
v___x_547_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_540_);
v___x_550_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_549_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_544_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_532_, v_fst_523_, v___x_552_, v___y_512_, v___y_513_);
lean_dec(v_fst_523_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; 
lean_dec_ref_known(v___x_553_, 1);
v___x_554_ = lean_box(0);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_510_, v___x_555_);
v_i_510_ = v___x_556_;
v_b_511_ = v___x_554_;
goto _start;
}
else
{
return v___x_553_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_565_, lean_object* v_sz_566_, lean_object* v_i_567_, lean_object* v_b_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_566_);
lean_dec(v_sz_566_);
v_i_boxed_573_ = lean_unbox_usize(v_i_567_);
lean_dec(v_i_567_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_565_, v_sz_boxed_572_, v_i_boxed_573_, v_b_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v_as_565_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_box(v___x_575_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v___x_22324__boxed_591_; lean_object* v_res_592_; 
v___x_22324__boxed_591_ = lean_unbox(v___x_584_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22324__boxed_591_, v_x_585_, v_x_586_, v_x_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec_ref(v_x_587_);
lean_dec_ref(v_x_586_);
lean_dec_ref(v_x_585_);
return v_res_592_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
uint8_t v___x_595_; 
v___x_595_ = 0;
return v___x_595_;
}
else
{
lean_object* v_key_596_; lean_object* v_tail_597_; uint8_t v___x_598_; 
v_key_596_ = lean_ctor_get(v_x_594_, 0);
v_tail_597_ = lean_ctor_get(v_x_594_, 2);
v___x_598_ = l_Lean_Syntax_instBEqRange_beq(v_key_596_, v_a_593_);
if (v___x_598_ == 0)
{
v_x_594_ = v_tail_597_;
goto _start;
}
else
{
return v___x_598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_600_, lean_object* v_x_601_){
_start:
{
uint8_t v_res_602_; lean_object* v_r_603_; 
v_res_602_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_600_, v_x_601_);
lean_dec(v_x_601_);
lean_dec_ref(v_a_600_);
v_r_603_ = lean_box(v_res_602_);
return v_r_603_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_buckets_606_; lean_object* v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v___x_610_; uint64_t v_fold_611_; uint64_t v___x_612_; uint64_t v___x_613_; uint64_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_buckets_606_ = lean_ctor_get(v_m_604_, 1);
v___x_607_ = lean_array_get_size(v_buckets_606_);
v___x_608_ = l_Lean_Syntax_instHashableRange_hash(v_a_605_);
v___x_609_ = 32ULL;
v___x_610_ = lean_uint64_shift_right(v___x_608_, v___x_609_);
v_fold_611_ = lean_uint64_xor(v___x_608_, v___x_610_);
v___x_612_ = 16ULL;
v___x_613_ = lean_uint64_shift_right(v_fold_611_, v___x_612_);
v___x_614_ = lean_uint64_xor(v_fold_611_, v___x_613_);
v___x_615_ = lean_uint64_to_usize(v___x_614_);
v___x_616_ = lean_usize_of_nat(v___x_607_);
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_sub(v___x_616_, v___x_617_);
v___x_619_ = lean_usize_land(v___x_615_, v___x_618_);
v___x_620_ = lean_array_uget_borrowed(v_buckets_606_, v___x_619_);
v___x_621_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_605_, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_622_, lean_object* v_a_623_){
_start:
{
uint8_t v_res_624_; lean_object* v_r_625_; 
v_res_624_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_622_, v_a_623_);
lean_dec_ref(v_a_623_);
lean_dec_ref(v_m_622_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v_x_628_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_dec(v_b_627_);
lean_dec_ref(v_a_626_);
return v_x_628_;
}
else
{
lean_object* v_key_629_; lean_object* v_value_630_; lean_object* v_tail_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_643_; 
v_key_629_ = lean_ctor_get(v_x_628_, 0);
v_value_630_ = lean_ctor_get(v_x_628_, 1);
v_tail_631_ = lean_ctor_get(v_x_628_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_628_);
if (v_isSharedCheck_643_ == 0)
{
v___x_633_ = v_x_628_;
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_tail_631_);
lean_inc(v_value_630_);
lean_inc(v_key_629_);
lean_dec(v_x_628_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_643_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_Syntax_instBEqRange_beq(v_key_629_, v_a_626_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_626_, v_b_627_, v_tail_631_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 2, v___x_636_);
v___x_638_ = v___x_633_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_key_629_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_value_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v___x_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v___x_641_; 
lean_dec(v_value_630_);
lean_dec(v_key_629_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_b_627_);
lean_ctor_set(v___x_633_, 0, v_a_626_);
v___x_641_ = v___x_633_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_626_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_b_627_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_tail_631_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
return v_x_644_;
}
else
{
lean_object* v_key_646_; lean_object* v_value_647_; lean_object* v_tail_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_671_; 
v_key_646_ = lean_ctor_get(v_x_645_, 0);
v_value_647_ = lean_ctor_get(v_x_645_, 1);
v_tail_648_ = lean_ctor_get(v_x_645_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_671_ == 0)
{
v___x_650_ = v_x_645_;
v_isShared_651_ = v_isSharedCheck_671_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_tail_648_);
lean_inc(v_value_647_);
lean_inc(v_key_646_);
lean_dec(v_x_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_671_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; uint64_t v___x_655_; uint64_t v_fold_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v___x_659_; size_t v___x_660_; size_t v___x_661_; size_t v___x_662_; size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_652_ = lean_array_get_size(v_x_644_);
v___x_653_ = l_Lean_Syntax_instHashableRange_hash(v_key_646_);
v___x_654_ = 32ULL;
v___x_655_ = lean_uint64_shift_right(v___x_653_, v___x_654_);
v_fold_656_ = lean_uint64_xor(v___x_653_, v___x_655_);
v___x_657_ = 16ULL;
v___x_658_ = lean_uint64_shift_right(v_fold_656_, v___x_657_);
v___x_659_ = lean_uint64_xor(v_fold_656_, v___x_658_);
v___x_660_ = lean_uint64_to_usize(v___x_659_);
v___x_661_ = lean_usize_of_nat(v___x_652_);
v___x_662_ = ((size_t)1ULL);
v___x_663_ = lean_usize_sub(v___x_661_, v___x_662_);
v___x_664_ = lean_usize_land(v___x_660_, v___x_663_);
v___x_665_ = lean_array_uget_borrowed(v_x_644_, v___x_664_);
lean_inc(v___x_665_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 2, v___x_665_);
v___x_667_ = v___x_650_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_key_646_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_value_647_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_665_);
v___x_667_ = v_reuseFailAlloc_670_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_array_uset(v_x_644_, v___x_664_, v___x_667_);
v_x_644_ = v___x_668_;
v_x_645_ = v_tail_648_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_672_, lean_object* v_source_673_, lean_object* v_target_674_){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_array_get_size(v_source_673_);
v___x_676_ = lean_nat_dec_lt(v_i_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_dec_ref(v_source_673_);
lean_dec(v_i_672_);
return v_target_674_;
}
else
{
lean_object* v_es_677_; lean_object* v___x_678_; lean_object* v_source_679_; lean_object* v_target_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v_es_677_ = lean_array_fget(v_source_673_, v_i_672_);
v___x_678_ = lean_box(0);
v_source_679_ = lean_array_fset(v_source_673_, v_i_672_, v___x_678_);
v_target_680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_674_, v_es_677_);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_nat_add(v_i_672_, v___x_681_);
lean_dec(v_i_672_);
v_i_672_ = v___x_682_;
v_source_673_ = v_source_679_;
v_target_674_ = v_target_680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_nbuckets_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_685_ = lean_array_get_size(v_data_684_);
v___x_686_ = lean_unsigned_to_nat(2u);
v_nbuckets_687_ = lean_nat_mul(v___x_685_, v___x_686_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_box(0);
v___x_690_ = lean_mk_array(v_nbuckets_687_, v___x_689_);
v___x_691_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_688_, v_data_684_, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_692_, lean_object* v_a_693_, lean_object* v_b_694_){
_start:
{
lean_object* v_size_695_; lean_object* v_buckets_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_739_; 
v_size_695_ = lean_ctor_get(v_m_692_, 0);
v_buckets_696_ = lean_ctor_get(v_m_692_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_m_692_);
if (v_isSharedCheck_739_ == 0)
{
v___x_698_ = v_m_692_;
v_isShared_699_ = v_isSharedCheck_739_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_buckets_696_);
lean_inc(v_size_695_);
lean_dec(v_m_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_739_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v___x_703_; uint64_t v_fold_704_; uint64_t v___x_705_; uint64_t v___x_706_; uint64_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v_bkt_713_; uint8_t v___x_714_; 
v___x_700_ = lean_array_get_size(v_buckets_696_);
v___x_701_ = l_Lean_Syntax_instHashableRange_hash(v_a_693_);
v___x_702_ = 32ULL;
v___x_703_ = lean_uint64_shift_right(v___x_701_, v___x_702_);
v_fold_704_ = lean_uint64_xor(v___x_701_, v___x_703_);
v___x_705_ = 16ULL;
v___x_706_ = lean_uint64_shift_right(v_fold_704_, v___x_705_);
v___x_707_ = lean_uint64_xor(v_fold_704_, v___x_706_);
v___x_708_ = lean_uint64_to_usize(v___x_707_);
v___x_709_ = lean_usize_of_nat(v___x_700_);
v___x_710_ = ((size_t)1ULL);
v___x_711_ = lean_usize_sub(v___x_709_, v___x_710_);
v___x_712_ = lean_usize_land(v___x_708_, v___x_711_);
v_bkt_713_ = lean_array_uget_borrowed(v_buckets_696_, v___x_712_);
v___x_714_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_693_, v_bkt_713_);
if (v___x_714_ == 0)
{
lean_object* v___x_715_; lean_object* v_size_x27_716_; lean_object* v___x_717_; lean_object* v_buckets_x27_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v_size_x27_716_ = lean_nat_add(v_size_695_, v___x_715_);
lean_dec(v_size_695_);
lean_inc(v_bkt_713_);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v_a_693_);
lean_ctor_set(v___x_717_, 1, v_b_694_);
lean_ctor_set(v___x_717_, 2, v_bkt_713_);
v_buckets_x27_718_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(4u);
v___x_720_ = lean_nat_mul(v_size_x27_716_, v___x_719_);
v___x_721_ = lean_unsigned_to_nat(3u);
v___x_722_ = lean_nat_div(v___x_720_, v___x_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_array_get_size(v_buckets_x27_718_);
v___x_724_ = lean_nat_dec_le(v___x_722_, v___x_723_);
lean_dec(v___x_722_);
if (v___x_724_ == 0)
{
lean_object* v_val_725_; lean_object* v___x_727_; 
v_val_725_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_718_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_val_725_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_727_ = v___x_698_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_val_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v___x_730_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_buckets_x27_718_);
lean_ctor_set(v___x_698_, 0, v_size_x27_716_);
v___x_730_ = v___x_698_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_size_x27_716_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_buckets_x27_718_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
else
{
lean_object* v___x_732_; lean_object* v_buckets_x27_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc(v_bkt_713_);
v___x_732_ = lean_box(0);
v_buckets_x27_733_ = lean_array_uset(v_buckets_696_, v___x_712_, v___x_732_);
v___x_734_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_693_, v_b_694_, v_bkt_713_);
v___x_735_ = lean_array_uset(v_buckets_x27_733_, v___x_712_, v___x_734_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_735_);
v___x_737_ = v___x_698_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_size_695_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_740_, lean_object* v_val_741_, lean_object* v_info_742_, lean_object* v___x_743_, lean_object* v_val_744_, uint8_t v___x_745_, lean_object* v_as_x27_746_, lean_object* v_b_747_, lean_object* v___y_748_){
_start:
{
if (lean_obj_tag(v_as_x27_746_) == 0)
{
lean_object* v___x_750_; 
lean_dec_ref(v_val_744_);
lean_dec(v___x_743_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v_b_747_);
return v___x_750_;
}
else
{
lean_object* v_head_751_; lean_object* v_tail_752_; lean_object* v___x_753_; lean_object* v_env_754_; lean_object* v___x_755_; lean_object* v___x_768_; 
v_head_751_ = lean_ctor_get(v_as_x27_746_, 0);
v_tail_752_ = lean_ctor_get(v_as_x27_746_, 1);
v___x_753_ = lean_st_ref_get(v___y_748_);
v_env_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc_ref(v_env_754_);
lean_dec(v___x_753_);
v___x_755_ = lean_box(0);
lean_inc(v_head_751_);
v___x_768_ = l_Lean_Environment_find_x3f(v_env_754_, v_head_751_, v___x_745_);
if (lean_obj_tag(v___x_768_) == 1)
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_768_, 1);
if (lean_obj_tag(v_val_769_) == 6)
{
lean_object* v_val_770_; lean_object* v_numFields_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_val_770_ = lean_ctor_get(v_val_769_, 0);
lean_inc_ref(v_val_770_);
lean_dec_ref_known(v_val_769_, 1);
v_numFields_771_ = lean_ctor_get(v_val_770_, 4);
lean_inc(v_numFields_771_);
lean_dec_ref(v_val_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_nat_dec_lt(v___x_772_, v_numFields_771_);
lean_dec(v_numFields_771_);
if (v___x_773_ == 0)
{
goto v___jp_756_;
}
else
{
v_as_x27_746_ = v_tail_752_;
v_b_747_ = v___x_755_;
goto _start;
}
}
else
{
lean_dec(v_val_769_);
goto v___jp_756_;
}
}
else
{
lean_dec(v___x_768_);
goto v___jp_756_;
}
v___jp_756_:
{
if (lean_obj_tag(v_head_751_) == 1)
{
lean_object* v_str_757_; uint8_t v___x_758_; 
v_str_757_ = lean_ctor_get(v_head_751_, 1);
v___x_758_ = lean_string_dec_eq(v_str_757_, v_str_740_);
if (v___x_758_ == 0)
{
v_as_x27_746_ = v_tail_752_;
v_b_747_ = v___x_755_;
goto _start;
}
else
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_760_ = lean_st_ref_take(v_val_741_);
v___x_761_ = l_Lean_Elab_Info_stx(v_info_742_);
lean_inc_ref(v_head_751_);
lean_inc(v___x_743_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_743_);
lean_ctor_set(v___x_762_, 1, v_head_751_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
lean_inc_ref(v_val_744_);
v___x_764_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_760_, v_val_744_, v___x_763_);
v___x_765_ = lean_st_ref_set(v_val_741_, v___x_764_);
v_as_x27_746_ = v_tail_752_;
v_b_747_ = v___x_755_;
goto _start;
}
}
else
{
v_as_x27_746_ = v_tail_752_;
v_b_747_ = v___x_755_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_775_, lean_object* v_val_776_, lean_object* v_info_777_, lean_object* v___x_778_, lean_object* v_val_779_, lean_object* v___x_780_, lean_object* v_as_x27_781_, lean_object* v_b_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v___x_22588__boxed_785_; lean_object* v_res_786_; 
v___x_22588__boxed_785_ = lean_unbox(v___x_780_);
v_res_786_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_775_, v_val_776_, v_info_777_, v___x_778_, v_val_779_, v___x_22588__boxed_785_, v_as_x27_781_, v_b_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec(v_as_x27_781_);
lean_dec_ref(v_info_777_);
lean_dec(v_val_776_);
lean_dec_ref(v_str_775_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_787_, v___y_789_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = lean_whnf(v_a_794_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
return v___x_795_;
}
else
{
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_803_, lean_object* v___x_804_, lean_object* v_val_805_, lean_object* v___x_806_, lean_object* v_ci_807_, lean_object* v_info_808_, lean_object* v_x_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
if (lean_obj_tag(v_info_808_) == 1)
{
lean_object* v_i_813_; lean_object* v_expr_814_; 
v_i_813_ = lean_ctor_get(v_info_808_, 0);
v_expr_814_ = lean_ctor_get(v_i_813_, 3);
if (lean_obj_tag(v_expr_814_) == 1)
{
lean_object* v_lctx_815_; lean_object* v_expectedType_x3f_816_; uint8_t v_isBinder_817_; lean_object* v_fvarId_818_; lean_object* v___x_819_; 
v_lctx_815_ = lean_ctor_get(v_i_813_, 1);
v_expectedType_x3f_816_ = lean_ctor_get(v_i_813_, 2);
v_isBinder_817_ = lean_ctor_get_uint8(v_i_813_, sizeof(void*)*4);
v_fvarId_818_ = lean_ctor_get(v_expr_814_, 0);
v___x_819_ = l_Lean_Elab_Info_range_x3f(v_info_808_);
if (lean_obj_tag(v___x_819_) == 1)
{
lean_object* v_val_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_975_; 
v_val_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_975_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_975_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_val_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_975_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_st_ref_get(v_val_803_);
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_824_, v_val_820_);
lean_dec(v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = l_Lean_Elab_Info_stx(v_info_808_);
v___x_827_ = l_Lean_Syntax_getHeadInfo(v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_dec_ref_known(v___x_827_, 4);
if (v_isBinder_817_ == 0)
{
lean_object* v___x_829_; 
lean_dec(v___x_826_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_804_);
v___x_829_ = v___x_822_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_804_);
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
lean_object* v___x_831_; 
lean_inc(v_fvarId_818_);
lean_inc_ref(v_lctx_815_);
v___x_831_ = lean_local_ctx_find(v_lctx_815_, v_fvarId_818_);
if (lean_obj_tag(v___x_831_) == 1)
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_965_; 
v_val_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_965_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_965_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_965_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_start_836_; uint8_t v___x_837_; 
v_start_836_ = lean_ctor_get(v_val_820_, 0);
v___x_837_ = l_Lean_Syntax_Range_contains(v_val_805_, v_start_836_, v___x_825_);
if (v___x_837_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v_val_832_);
lean_dec(v___x_826_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_804_);
v___x_839_ = v___x_834_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_804_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
if (v___x_825_ == 0)
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = l_Lean_LocalDecl_userName(v_val_832_);
lean_dec(v_val_832_);
v___x_842_ = l_Lean_Name_hasMacroScopes(v___x_841_);
lean_dec(v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v_toCommandContextInfo_843_; lean_object* v_options_844_; lean_object* v___x_845_; 
v_toCommandContextInfo_843_ = lean_ctor_get(v_ci_807_, 0);
v_options_844_ = lean_ctor_get(v_toCommandContextInfo_843_, 4);
lean_inc_ref(v_options_844_);
v___x_845_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_844_, v___y_811_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_950_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_950_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_950_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_950_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
uint8_t v___x_850_; 
v___x_850_ = l_Lean_Linter_getLinterValue(v___x_806_, v_a_846_);
lean_dec(v_a_846_);
if (v___x_850_ == 0)
{
lean_object* v___x_852_; 
lean_del_object(v___x_834_);
lean_dec(v___x_826_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_804_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_804_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
else
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Syntax_getId(v___x_826_);
lean_dec(v___x_826_);
if (lean_obj_tag(v___x_854_) == 1)
{
lean_object* v_pre_855_; lean_object* v_str_856_; lean_object* v_ty_858_; lean_object* v___y_859_; lean_object* v___y_860_; 
v_pre_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_pre_855_);
v_str_856_ = lean_ctor_get(v___x_854_, 1);
lean_inc_ref(v_str_856_);
if (lean_obj_tag(v_pre_855_) == 0)
{
lean_del_object(v___x_848_);
if (lean_obj_tag(v_expectedType_x3f_816_) == 1)
{
lean_object* v_val_917_; 
lean_del_object(v___x_822_);
v_val_917_ = lean_ctor_get(v_expectedType_x3f_816_, 0);
lean_inc(v_val_917_);
v_ty_858_ = v_val_917_;
v___y_859_ = v___y_810_;
v___y_860_ = v___y_811_;
goto v___jp_857_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc_ref(v_expr_814_);
v___x_918_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_918_, 0, v_expr_814_);
lean_inc_ref(v_ci_807_);
lean_inc_ref(v_i_813_);
v___x_919_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_813_, v_ci_807_, v___x_918_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; 
lean_del_object(v___x_822_);
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v_ty_858_ = v_a_920_;
v___y_859_ = v___y_810_;
v___y_860_ = v___y_811_;
goto v___jp_857_;
}
else
{
lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_str_856_);
lean_dec_ref_known(v___x_854_, 2);
lean_del_object(v___x_834_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
v_isSharedCheck_941_ = !lean_is_exclusive(v_val_820_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; lean_object* v_unused_943_; 
v_unused_942_ = lean_ctor_get(v_val_820_, 1);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_val_820_, 0);
lean_dec(v_unused_943_);
v___x_922_ = v_val_820_;
v_isShared_923_ = v_isSharedCheck_941_;
goto v_resetjp_921_;
}
else
{
lean_dec(v_val_820_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_941_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_940_; 
v_a_924_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_940_ == 0)
{
v___x_926_ = v___x_919_;
v_isShared_927_ = v_isSharedCheck_940_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_940_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_ref_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v_ref_928_ = lean_ctor_get(v___y_810_, 7);
v___x_929_ = lean_io_error_to_string(v_a_924_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 3);
lean_ctor_set(v___x_822_, 0, v___x_929_);
v___x_931_ = v___x_822_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_939_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_Lean_MessageData_ofFormat(v___x_931_);
lean_inc(v_ref_928_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_932_);
lean_ctor_set(v___x_922_, 0, v_ref_928_);
v___x_934_ = v___x_922_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_ref_928_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___x_932_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_934_);
v___x_936_ = v___x_926_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
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
lean_object* v___x_945_; 
lean_dec_ref(v_str_856_);
lean_dec(v_pre_855_);
lean_dec_ref_known(v___x_854_, 2);
lean_del_object(v___x_834_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_804_);
v___x_945_ = v___x_848_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_804_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
v___jp_857_:
{
lean_object* v___f_861_; lean_object* v___x_862_; 
v___f_861_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_861_, 0, v_ty_858_);
lean_inc_ref(v_i_813_);
v___x_862_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_813_, v_ci_807_, v___f_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_893_; 
lean_del_object(v___x_834_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_893_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_893_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_893_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Expr_getAppFn_x27(v_a_863_);
lean_dec(v_a_863_);
if (lean_obj_tag(v___x_867_) == 4)
{
lean_object* v_declName_868_; lean_object* v___x_869_; lean_object* v_env_870_; lean_object* v___x_871_; 
v_declName_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_declName_868_);
lean_dec_ref_known(v___x_867_, 2);
v___x_869_ = lean_st_ref_get(v___y_860_);
v_env_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_env_870_);
lean_dec(v___x_869_);
v___x_871_ = l_Lean_Environment_find_x3f(v_env_870_, v_declName_868_, v___x_825_);
if (lean_obj_tag(v___x_871_) == 1)
{
lean_object* v_val_872_; 
v_val_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_871_, 1);
if (lean_obj_tag(v_val_872_) == 5)
{
lean_object* v_val_873_; lean_object* v_ctors_874_; lean_object* v___x_875_; 
lean_del_object(v___x_865_);
v_val_873_ = lean_ctor_get(v_val_872_, 0);
lean_inc_ref(v_val_873_);
lean_dec_ref_known(v_val_872_, 1);
v_ctors_874_ = lean_ctor_get(v_val_873_, 4);
lean_inc(v_ctors_874_);
lean_dec_ref(v_val_873_);
v___x_875_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_856_, v_val_803_, v_info_808_, v___x_854_, v_val_820_, v___x_825_, v_ctors_874_, v___x_804_, v___y_860_);
lean_dec(v_ctors_874_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_str_856_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v___x_875_, 0);
lean_dec(v_unused_883_);
v___x_877_ = v___x_875_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_875_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_804_);
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_804_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
return v___x_875_;
}
}
else
{
lean_object* v___x_885_; 
lean_dec(v_val_872_);
lean_dec_ref(v_str_856_);
lean_dec_ref_known(v___x_854_, 2);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_804_);
v___x_885_ = v___x_865_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_804_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
else
{
lean_object* v___x_888_; 
lean_dec(v___x_871_);
lean_dec_ref(v_str_856_);
lean_dec_ref_known(v___x_854_, 2);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_804_);
v___x_888_ = v___x_865_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_804_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v___x_891_; 
lean_dec_ref(v___x_867_);
lean_dec_ref(v_str_856_);
lean_dec_ref_known(v___x_854_, 2);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_804_);
v___x_891_ = v___x_865_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_804_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_str_856_);
lean_dec_ref_known(v___x_854_, 2);
lean_dec_ref_known(v_info_808_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_val_820_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; lean_object* v_unused_916_; 
v_unused_915_ = lean_ctor_get(v_val_820_, 1);
lean_dec(v_unused_915_);
v_unused_916_ = lean_ctor_get(v_val_820_, 0);
lean_dec(v_unused_916_);
v___x_895_ = v_val_820_;
v_isShared_896_ = v_isSharedCheck_914_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_val_820_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_914_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_913_; 
v_a_897_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_913_ == 0)
{
v___x_899_ = v___x_862_;
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_862_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_ref_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v_ref_901_ = lean_ctor_get(v___y_859_, 7);
v___x_902_ = lean_io_error_to_string(v_a_897_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 3);
lean_ctor_set(v___x_834_, 0, v___x_902_);
v___x_904_ = v___x_834_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_912_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = l_Lean_MessageData_ofFormat(v___x_904_);
lean_inc(v_ref_901_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___x_905_);
lean_ctor_set(v___x_895_, 0, v_ref_901_);
v___x_907_ = v___x_895_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_ref_901_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_905_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_907_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
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
lean_object* v___x_948_; 
lean_dec(v___x_854_);
lean_del_object(v___x_834_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_804_);
v___x_948_ = v___x_848_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_804_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_del_object(v___x_834_);
lean_dec(v___x_826_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
v_a_951_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_845_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_845_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
else
{
lean_object* v___x_960_; 
lean_dec(v___x_826_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_804_);
v___x_960_ = v___x_834_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_804_);
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
lean_dec(v_val_832_);
lean_dec(v___x_826_);
lean_del_object(v___x_822_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_835_ == 0)
{
lean_ctor_set_tag(v___x_834_, 0);
lean_ctor_set(v___x_834_, 0, v___x_804_);
v___x_963_ = v___x_834_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_804_);
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
}
else
{
lean_object* v___x_967_; 
lean_dec(v___x_831_);
lean_dec(v___x_826_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_804_);
v___x_967_ = v___x_822_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_804_);
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
else
{
lean_object* v___x_970_; 
lean_dec(v___x_827_);
lean_dec(v___x_826_);
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_804_);
v___x_970_ = v___x_822_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_804_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v___x_973_; 
lean_dec(v_val_820_);
lean_dec_ref_known(v_info_808_, 1);
lean_dec_ref(v_ci_807_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_804_);
v___x_973_ = v___x_822_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_804_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v___x_819_);
lean_dec_ref(v_ci_807_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_info_808_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_info_808_, 0);
lean_dec(v_unused_983_);
v___x_977_ = v_info_808_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_dec(v_info_808_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 0);
lean_ctor_set(v___x_977_, 0, v___x_804_);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_804_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v_ci_807_);
v_isSharedCheck_990_ = !lean_is_exclusive(v_info_808_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v_info_808_, 0);
lean_dec(v_unused_991_);
v___x_985_ = v_info_808_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_dec(v_info_808_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
lean_ctor_set(v___x_985_, 0, v___x_804_);
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_804_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v___x_992_; 
lean_dec_ref(v_info_808_);
lean_dec_ref(v_ci_807_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_804_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_993_, lean_object* v___x_994_, lean_object* v_val_995_, lean_object* v___x_996_, lean_object* v_ci_997_, lean_object* v_info_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_993_, v___x_994_, v_val_995_, v___x_996_, v_ci_997_, v_info_998_, v_x_999_, v___y_1000_, v___y_1001_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec_ref(v_x_999_);
lean_dec_ref(v___x_996_);
lean_dec_ref(v_val_995_);
lean_dec(v_val_993_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_1004_, lean_object* v_ci_1005_, lean_object* v_i_1006_, lean_object* v_cs_1007_, lean_object* v_x_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
v___x_1012_ = lean_apply_6(v_postNode_1004_, v_ci_1005_, v_i_1006_, v_cs_1007_, v___y_1009_, v___y_1010_, lean_box(0));
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1013_, lean_object* v_ci_1014_, lean_object* v_i_1015_, lean_object* v_cs_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1013_, v_ci_1014_, v_i_1015_, v_cs_1016_, v_x_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v_x_1017_);
return v_res_1021_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_instMonadEIO(lean_box(0));
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_toApplicative_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1062_; 
v___x_1029_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1030_ = l_StateRefT_x27_instMonad___redArg(v___x_1029_);
v_toApplicative_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v___x_1030_, 1);
lean_dec(v_unused_1063_);
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1062_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_toApplicative_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1062_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_toFunctor_1035_; lean_object* v_toSeq_1036_; lean_object* v_toSeqLeft_1037_; lean_object* v_toSeqRight_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1060_; 
v_toFunctor_1035_ = lean_ctor_get(v_toApplicative_1031_, 0);
v_toSeq_1036_ = lean_ctor_get(v_toApplicative_1031_, 2);
v_toSeqLeft_1037_ = lean_ctor_get(v_toApplicative_1031_, 3);
v_toSeqRight_1038_ = lean_ctor_get(v_toApplicative_1031_, 4);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_toApplicative_1031_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_toApplicative_1031_, 1);
lean_dec(v_unused_1061_);
v___x_1040_ = v_toApplicative_1031_;
v_isShared_1041_ = v_isSharedCheck_1060_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_toSeqRight_1038_);
lean_inc(v_toSeqLeft_1037_);
lean_inc(v_toSeq_1036_);
lean_inc(v_toFunctor_1035_);
lean_dec(v_toApplicative_1031_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1060_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___f_1042_; lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___x_1051_; 
v___f_1042_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1043_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1035_);
v___f_1044_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1044_, 0, v_toFunctor_1035_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toFunctor_1035_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___f_1044_);
lean_ctor_set(v___x_1046_, 1, v___f_1045_);
v___f_1047_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1047_, 0, v_toSeqRight_1038_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeqLeft_1037_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeq_1036_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 4, v___f_1047_);
lean_ctor_set(v___x_1040_, 3, v___f_1048_);
lean_ctor_set(v___x_1040_, 2, v___f_1049_);
lean_ctor_set(v___x_1040_, 1, v___f_1042_);
lean_ctor_set(v___x_1040_, 0, v___x_1046_);
v___x_1051_ = v___x_1040_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___f_1042_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1059_, 3, v___f_1048_);
lean_ctor_set(v_reuseFailAlloc_1059_, 4, v___f_1047_);
v___x_1051_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___f_1043_);
lean_ctor_set(v___x_1033_, 0, v___x_1051_);
v___x_1053_ = v___x_1033_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___f_1043_);
v___x_1053_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_18815__overap_1056_; lean_object* v___x_1057_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = l_instInhabitedOfMonad___redArg(v___x_1053_, v___x_1054_);
v___x_18815__overap_1056_ = lean_panic_fn_borrowed(v___x_1055_, v_msg_1025_);
lean_dec(v___x_1055_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
v___x_1057_ = lean_apply_3(v___x_18815__overap_1056_, v___y_1026_, v___y_1027_, lean_box(0));
return v___x_1057_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
return v_res_1068_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1073_ = lean_unsigned_to_nat(21u);
v___x_1074_ = lean_unsigned_to_nat(65u);
v___x_1075_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1076_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1077_ = l_mkPanicMessageWithDecl(v___x_1076_, v___x_1075_, v___x_1074_, v___x_1073_, v___x_1072_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1078_, lean_object* v_postNode_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
switch(lean_obj_tag(v_x_1081_))
{
case 0:
{
lean_object* v_i_1085_; lean_object* v_t_1086_; lean_object* v___x_1087_; 
v_i_1085_ = lean_ctor_get(v_x_1081_, 0);
lean_inc_ref(v_i_1085_);
v_t_1086_ = lean_ctor_get(v_x_1081_, 1);
lean_inc_ref(v_t_1086_);
lean_dec_ref_known(v_x_1081_, 2);
v___x_1087_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1085_, v_x_1080_);
v_x_1080_ = v___x_1087_;
v_x_1081_ = v_t_1086_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref_known(v_x_1081_, 2);
lean_dec_ref(v_postNode_1079_);
lean_dec_ref(v_preNode_1078_);
v___x_1089_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1090_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1089_, v___y_1082_, v___y_1083_);
return v___x_1090_;
}
else
{
lean_object* v_i_1091_; lean_object* v_children_1092_; lean_object* v_val_1093_; lean_object* v___x_1094_; 
v_i_1091_ = lean_ctor_get(v_x_1081_, 0);
lean_inc_ref_n(v_i_1091_, 2);
v_children_1092_ = lean_ctor_get(v_x_1081_, 1);
lean_inc_ref_n(v_children_1092_, 2);
lean_dec_ref_known(v_x_1081_, 2);
v_val_1093_ = lean_ctor_get(v_x_1080_, 0);
lean_inc_n(v_val_1093_, 2);
lean_inc_ref(v_preNode_1078_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1094_ = lean_apply_6(v_preNode_1078_, v_val_1093_, v_i_1091_, v_children_1092_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; uint8_t v___x_1096_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = lean_unbox(v_a_1095_);
lean_dec(v_a_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1121_; 
lean_dec_ref(v_preNode_1078_);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_x_1080_, 0);
lean_dec(v_unused_1122_);
v___x_1098_ = v_x_1080_;
v_isShared_1099_ = v_isSharedCheck_1121_;
goto v_resetjp_1097_;
}
else
{
lean_dec(v_x_1080_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1121_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_box(0);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1101_ = lean_apply_7(v_postNode_1079_, v_val_1093_, v_i_1091_, v_children_1092_, v___x_1100_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1112_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v_a_1102_);
v___x_1107_ = v___x_1098_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1107_);
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
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
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_del_object(v___x_1098_);
v_a_1113_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1101_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1101_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1080_, v_i_1091_);
v___x_1124_ = l_Lean_PersistentArray_toList___redArg(v_children_1092_);
v___x_1125_ = lean_box(0);
lean_inc_ref(v_postNode_1079_);
v___x_1126_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1078_, v_postNode_1079_, v___x_1123_, v___x_1124_, v___x_1125_, v___y_1082_, v___y_1083_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref_known(v___x_1126_, 1);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1128_ = lean_apply_7(v_postNode_1079_, v_val_1093_, v_i_1091_, v_children_1092_, v_a_1127_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_a_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_a_1138_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1128_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1128_);
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
lean_dec(v_val_1093_);
lean_dec_ref(v_children_1092_);
lean_dec_ref(v_i_1091_);
lean_dec_ref(v_postNode_1079_);
v_a_1146_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1126_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1126_);
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
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_val_1093_);
lean_dec_ref(v_children_1092_);
lean_dec_ref(v_i_1091_);
lean_dec_ref_known(v_x_1080_, 1);
lean_dec_ref(v_postNode_1079_);
lean_dec_ref(v_preNode_1078_);
v_a_1154_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1094_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1094_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
default: 
{
lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_x_1080_);
lean_dec_ref(v_postNode_1079_);
lean_dec_ref(v_preNode_1078_);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1081_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v_x_1081_, 0);
lean_dec(v_unused_1170_);
v___x_1163_ = v_x_1081_;
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
else
{
lean_dec(v_x_1081_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1169_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1165_ = lean_box(0);
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1165_);
v___x_1167_ = v___x_1163_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1171_, lean_object* v_postNode_1172_, lean_object* v___x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec(v___x_1173_);
lean_dec_ref(v_postNode_1172_);
lean_dec_ref(v_preNode_1171_);
v___x_1179_ = l_List_reverse___redArg(v_x_1175_);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
else
{
lean_object* v_head_1181_; lean_object* v_tail_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1200_; 
v_head_1181_ = lean_ctor_get(v_x_1174_, 0);
v_tail_1182_ = lean_ctor_get(v_x_1174_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1184_ = v_x_1174_;
v_isShared_1185_ = v_isSharedCheck_1200_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_tail_1182_);
lean_inc(v_head_1181_);
lean_dec(v_x_1174_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1200_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; 
lean_inc(v___x_1173_);
lean_inc_ref(v_postNode_1172_);
lean_inc_ref(v_preNode_1171_);
v___x_1186_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1171_, v_postNode_1172_, v___x_1173_, v_head_1181_, v___y_1176_, v___y_1177_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 1, v_x_1175_);
lean_ctor_set(v___x_1184_, 0, v_a_1187_);
v___x_1189_ = v___x_1184_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1187_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_x_1175_);
v___x_1189_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
v_x_1174_ = v_tail_1182_;
v_x_1175_ = v___x_1189_;
goto _start;
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1184_);
lean_dec(v_tail_1182_);
lean_dec(v_x_1175_);
lean_dec(v___x_1173_);
lean_dec_ref(v_postNode_1172_);
lean_dec_ref(v_preNode_1171_);
v_a_1192_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1186_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1186_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1201_, lean_object* v_postNode_1202_, lean_object* v___x_1203_, lean_object* v_x_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1201_, v_postNode_1202_, v___x_1203_, v_x_1204_, v_x_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1210_, lean_object* v_postNode_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1210_, v_postNode_1211_, v_x_1212_, v_x_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1218_, lean_object* v_postNode_1219_, lean_object* v_ctx_x3f_1220_, lean_object* v_t_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___f_1225_; lean_object* v___x_1226_; 
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1225_, 0, v_postNode_1219_);
v___x_1226_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1218_, v___f_1225_, v_ctx_x3f_1220_, v_t_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1234_; 
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1234_ == 0)
{
lean_object* v_unused_1235_; 
v_unused_1235_ = lean_ctor_get(v___x_1226_, 0);
lean_dec(v_unused_1235_);
v___x_1228_ = v___x_1226_;
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
else
{
lean_dec(v___x_1226_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1234_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1230_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1230_);
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_a_1236_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1226_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1226_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1244_, lean_object* v_postNode_1245_, lean_object* v_ctx_x3f_1246_, lean_object* v_t_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1244_, v_postNode_1245_, v_ctx_x3f_1246_, v_t_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1252_, lean_object* v_val_1253_, lean_object* v_val_1254_, lean_object* v_as_1255_, size_t v_sz_1256_, size_t v_i_1257_, lean_object* v_b_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_lt(v_i_1257_, v_sz_1256_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref(v_val_1254_);
lean_dec(v_val_1253_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_b_1258_);
return v___x_1263_;
}
else
{
lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___f_1268_; lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1264_ = lean_box(v___x_1252_);
v___f_1265_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1265_, 0, v___x_1264_);
v___x_1266_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1267_ = lean_box(0);
lean_inc_ref(v_val_1254_);
lean_inc(v_val_1253_);
v___f_1268_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1268_, 0, v_val_1253_);
lean_closure_set(v___f_1268_, 1, v___x_1267_);
lean_closure_set(v___f_1268_, 2, v_val_1254_);
lean_closure_set(v___f_1268_, 3, v___x_1266_);
v_a_1269_ = lean_array_uget_borrowed(v_as_1255_, v_i_1257_);
v___x_1270_ = lean_box(0);
lean_inc(v_a_1269_);
v___x_1271_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1265_, v___f_1268_, v___x_1270_, v_a_1269_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1271_) == 0)
{
size_t v___x_1272_; size_t v___x_1273_; 
lean_dec_ref_known(v___x_1271_, 1);
v___x_1272_ = ((size_t)1ULL);
v___x_1273_ = lean_usize_add(v_i_1257_, v___x_1272_);
v_i_1257_ = v___x_1273_;
v_b_1258_ = v___x_1267_;
goto _start;
}
else
{
lean_dec_ref(v_val_1254_);
lean_dec(v_val_1253_);
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1275_, lean_object* v_val_1276_, lean_object* v_val_1277_, lean_object* v_as_1278_, lean_object* v_sz_1279_, lean_object* v_i_1280_, lean_object* v_b_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_23452__boxed_1285_; size_t v_sz_boxed_1286_; size_t v_i_boxed_1287_; lean_object* v_res_1288_; 
v___x_23452__boxed_1285_ = lean_unbox(v___x_1275_);
v_sz_boxed_1286_ = lean_unbox_usize(v_sz_1279_);
lean_dec(v_sz_1279_);
v_i_boxed_1287_ = lean_unbox_usize(v_i_1280_);
lean_dec(v_i_1280_);
v_res_1288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23452__boxed_1285_, v_val_1276_, v_val_1277_, v_as_1278_, v_sz_boxed_1286_, v_i_boxed_1287_, v_b_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec_ref(v_as_1278_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
return v_x_1289_;
}
else
{
lean_object* v_key_1291_; lean_object* v_value_1292_; lean_object* v_tail_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_key_1291_ = lean_ctor_get(v_x_1290_, 0);
v_value_1292_ = lean_ctor_get(v_x_1290_, 1);
v_tail_1293_ = lean_ctor_get(v_x_1290_, 2);
lean_inc(v_value_1292_);
lean_inc(v_key_1291_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_key_1291_);
lean_ctor_set(v___x_1294_, 1, v_value_1292_);
v___x_1295_ = lean_array_push(v_x_1289_, v___x_1294_);
v_x_1289_ = v___x_1295_;
v_x_1290_ = v_tail_1293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1297_, v_x_1298_);
lean_dec(v_x_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1300_, size_t v_i_1301_, size_t v_stop_1302_, lean_object* v_b_1303_){
_start:
{
uint8_t v___x_1304_; 
v___x_1304_ = lean_usize_dec_eq(v_i_1301_, v_stop_1302_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; size_t v___x_1307_; size_t v___x_1308_; 
v___x_1305_ = lean_array_uget_borrowed(v_as_1300_, v_i_1301_);
v___x_1306_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1303_, v___x_1305_);
v___x_1307_ = ((size_t)1ULL);
v___x_1308_ = lean_usize_add(v_i_1301_, v___x_1307_);
v_i_1301_ = v___x_1308_;
v_b_1303_ = v___x_1306_;
goto _start;
}
else
{
return v_b_1303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1310_, lean_object* v_i_1311_, lean_object* v_stop_1312_, lean_object* v_b_1313_){
_start:
{
size_t v_i_boxed_1314_; size_t v_stop_boxed_1315_; lean_object* v_res_1316_; 
v_i_boxed_1314_ = lean_unbox_usize(v_i_1311_);
lean_dec(v_i_1311_);
v_stop_boxed_1315_ = lean_unbox_usize(v_stop_1312_);
lean_dec(v_stop_1312_);
v_res_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1310_, v_i_boxed_1314_, v_stop_boxed_1315_, v_b_1313_);
lean_dec_ref(v_as_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v_scopes_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_opts_1324_; lean_object* v___x_1325_; 
v___x_1320_ = lean_st_ref_get(v___y_1318_);
v_scopes_1321_ = lean_ctor_get(v___x_1320_, 2);
lean_inc(v_scopes_1321_);
lean_dec(v___x_1320_);
v___x_1322_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1323_ = l_List_head_x21___redArg(v___x_1322_, v_scopes_1321_);
lean_dec(v_scopes_1321_);
v_opts_1324_ = lean_ctor_get(v___x_1323_, 1);
lean_inc_ref(v_opts_1324_);
lean_dec(v___x_1323_);
v___x_1325_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1324_, v___y_1318_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_unsigned_to_nat(16u);
v___x_1332_ = lean_mk_array(v___x_1331_, v___x_1330_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___x_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___x_1333_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1411_; 
v___x_1340_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1337_, v___y_1338_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1411_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1411_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1345_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1346_ = l_Lean_Linter_getLinterValue(v___x_1345_, v_a_1341_);
lean_dec(v_a_1341_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_box(0);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1347_);
v___x_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
uint8_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = 0;
v___x_1352_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1336_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_infoState_1358_; lean_object* v_trees_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; size_t v_sz_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
lean_del_object(v___x_1343_);
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = lean_st_ref_get(v___y_1338_);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1357_ = lean_st_mk_ref(v___x_1356_);
v_infoState_1358_ = lean_ctor_get(v___x_1354_, 8);
lean_inc_ref(v_infoState_1358_);
lean_dec(v___x_1354_);
v_trees_1359_ = lean_ctor_get(v_infoState_1358_, 2);
lean_inc_ref(v_trees_1359_);
lean_dec_ref(v_infoState_1358_);
v___x_1360_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1359_);
lean_dec_ref(v_trees_1359_);
v___x_1361_ = lean_box(0);
v_sz_1362_ = lean_array_size(v___x_1360_);
v___x_1363_ = ((size_t)0ULL);
lean_inc(v___x_1357_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1346_, v___x_1357_, v_val_1353_, v___x_1360_, v_sz_1362_, v___x_1363_, v___x_1361_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___x_1360_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; lean_object* v___y_1367_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1391_; lean_object* v_size_1397_; lean_object* v_buckets_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; uint8_t v___x_1401_; 
lean_dec_ref_known(v___x_1364_, 1);
v___x_1365_ = lean_st_ref_get(v___x_1357_);
lean_dec(v___x_1357_);
v_size_1397_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_size_1397_);
v_buckets_1398_ = lean_ctor_get(v___x_1365_, 1);
lean_inc_ref(v_buckets_1398_);
lean_dec(v___x_1365_);
v___x_1399_ = lean_mk_empty_array_with_capacity(v_size_1397_);
lean_dec(v_size_1397_);
v___x_1400_ = lean_array_get_size(v_buckets_1398_);
v___x_1401_ = lean_nat_dec_lt(v___x_1355_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_dec_ref(v_buckets_1398_);
v___y_1391_ = v___x_1399_;
goto v___jp_1390_;
}
else
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_le(v___x_1400_, v___x_1400_);
if (v___x_1402_ == 0)
{
if (v___x_1401_ == 0)
{
lean_dec_ref(v_buckets_1398_);
v___y_1391_ = v___x_1399_;
goto v___jp_1390_;
}
else
{
size_t v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = lean_usize_of_nat(v___x_1400_);
v___x_1404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1398_, v___x_1363_, v___x_1403_, v___x_1399_);
lean_dec_ref(v_buckets_1398_);
v___y_1391_ = v___x_1404_;
goto v___jp_1390_;
}
}
else
{
size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1405_ = lean_usize_of_nat(v___x_1400_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1398_, v___x_1363_, v___x_1405_, v___x_1399_);
lean_dec_ref(v_buckets_1398_);
v___y_1391_ = v___x_1406_;
goto v___jp_1390_;
}
}
v___jp_1366_:
{
size_t v_sz_1368_; lean_object* v___x_1369_; 
v_sz_1368_ = lean_array_size(v___y_1367_);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1367_, v_sz_1368_, v___x_1363_, v___x_1361_, v___y_1337_, v___y_1338_);
lean_dec_ref(v___y_1367_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v___x_1369_, 0);
lean_dec(v_unused_1377_);
v___x_1371_ = v___x_1369_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v___x_1369_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1361_);
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1361_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
else
{
return v___x_1369_;
}
}
v___jp_1378_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1379_, v___y_1381_, v___y_1380_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec(v___y_1379_);
v___y_1367_ = v___x_1383_;
goto v___jp_1366_;
}
v___jp_1384_:
{
uint8_t v___x_1389_; 
v___x_1389_ = lean_nat_dec_le(v___y_1388_, v___y_1386_);
if (v___x_1389_ == 0)
{
lean_dec(v___y_1386_);
lean_inc(v___y_1388_);
v___y_1379_ = v___y_1385_;
v___y_1380_ = v___y_1388_;
v___y_1381_ = v___y_1387_;
v___y_1382_ = v___y_1388_;
goto v___jp_1378_;
}
else
{
v___y_1379_ = v___y_1385_;
v___y_1380_ = v___y_1388_;
v___y_1381_ = v___y_1387_;
v___y_1382_ = v___y_1386_;
goto v___jp_1378_;
}
}
v___jp_1390_:
{
lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = lean_array_get_size(v___y_1391_);
v___x_1393_ = lean_nat_dec_eq(v___x_1392_, v___x_1355_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_unsigned_to_nat(1u);
v___x_1395_ = lean_nat_sub(v___x_1392_, v___x_1394_);
v___x_1396_ = lean_nat_dec_le(v___x_1355_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_inc(v___x_1395_);
v___y_1385_ = v___x_1392_;
v___y_1386_ = v___x_1395_;
v___y_1387_ = v___y_1391_;
v___y_1388_ = v___x_1395_;
goto v___jp_1384_;
}
else
{
v___y_1385_ = v___x_1392_;
v___y_1386_ = v___x_1395_;
v___y_1387_ = v___y_1391_;
v___y_1388_ = v___x_1355_;
goto v___jp_1384_;
}
}
else
{
v___y_1367_ = v___y_1391_;
goto v___jp_1366_;
}
}
}
else
{
lean_dec(v___x_1357_);
return v___x_1364_;
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v___x_1352_);
v___x_1407_ = lean_box(0);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1407_);
v___x_1409_ = v___x_1343_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v_cmdStx_1412_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_){
_start:
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1427_, v_a_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_){
_start:
{
uint8_t v_res_1433_; lean_object* v_r_1434_; 
v_res_1433_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1430_, v_m_1431_, v_a_1432_);
lean_dec_ref(v_a_1432_);
lean_dec_ref(v_m_1431_);
v_r_1434_ = lean_box(v_res_1433_);
return v_r_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_, lean_object* v_b_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1436_, v_a_1437_, v_b_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1440_, lean_object* v_val_1441_, lean_object* v_info_1442_, lean_object* v___x_1443_, lean_object* v_val_1444_, uint8_t v___x_1445_, lean_object* v_as_1446_, lean_object* v_as_x27_1447_, lean_object* v_b_1448_, lean_object* v_a_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1440_, v_val_1441_, v_info_1442_, v___x_1443_, v_val_1444_, v___x_1445_, v_as_x27_1447_, v_b_1448_, v___y_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1454_, lean_object* v_val_1455_, lean_object* v_info_1456_, lean_object* v___x_1457_, lean_object* v_val_1458_, lean_object* v___x_1459_, lean_object* v_as_1460_, lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v_a_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v___x_23744__boxed_1467_; lean_object* v_res_1468_; 
v___x_23744__boxed_1467_ = lean_unbox(v___x_1459_);
v_res_1468_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1454_, v_val_1455_, v_info_1456_, v___x_1457_, v_val_1458_, v___x_23744__boxed_1467_, v_as_1460_, v_as_x27_1461_, v_b_1462_, v_a_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_as_x27_1461_);
lean_dec(v_as_1460_);
lean_dec_ref(v_info_1456_);
lean_dec(v_val_1455_);
lean_dec_ref(v_str_1454_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1469_, lean_object* v_as_1470_, lean_object* v_lo_1471_, lean_object* v_hi_1472_, lean_object* v_w_1473_, lean_object* v_hlo_1474_, lean_object* v_hhi_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1469_, v_as_1470_, v_lo_1471_, v_hi_1472_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1477_, lean_object* v_as_1478_, lean_object* v_lo_1479_, lean_object* v_hi_1480_, lean_object* v_w_1481_, lean_object* v_hlo_1482_, lean_object* v_hhi_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1477_, v_as_1478_, v_lo_1479_, v_hi_1480_, v_w_1481_, v_hlo_1482_, v_hhi_1483_);
lean_dec(v_hi_1480_);
lean_dec(v_n_1477_);
return v_res_1484_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1485_, lean_object* v_a_1486_, lean_object* v_x_1487_){
_start:
{
uint8_t v___x_1488_; 
v___x_1488_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1486_, v_x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1489_, lean_object* v_a_1490_, lean_object* v_x_1491_){
_start:
{
uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_res_1492_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1489_, v_a_1490_, v_x_1491_);
lean_dec(v_x_1491_);
lean_dec_ref(v_a_1490_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1494_, lean_object* v_data_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1497_, lean_object* v_a_1498_, lean_object* v_b_1499_, lean_object* v_x_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1498_, v_b_1499_, v_x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1502_, lean_object* v_msg_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1503_, v___y_1504_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_msg_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1508_, v_msg_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1514_, lean_object* v_preNode_1515_, lean_object* v_postNode_1516_, lean_object* v_x_1517_, lean_object* v_x_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1515_, v_postNode_1516_, v_x_1517_, v_x_1518_, v___y_1519_, v___y_1520_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1523_, lean_object* v_preNode_1524_, lean_object* v_postNode_1525_, lean_object* v_x_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1523_, v_preNode_1524_, v_postNode_1525_, v_x_1526_, v_x_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object* v_n_1532_, lean_object* v_lo_1533_, lean_object* v_hi_1534_, lean_object* v_hhi_1535_, lean_object* v_pivot_1536_, lean_object* v_as_1537_, lean_object* v_i_1538_, lean_object* v_k_1539_, lean_object* v_ilo_1540_, lean_object* v_ik_1541_, lean_object* v_w_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1534_, v_pivot_1536_, v_as_1537_, v_i_1538_, v_k_1539_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object* v_n_1544_, lean_object* v_lo_1545_, lean_object* v_hi_1546_, lean_object* v_hhi_1547_, lean_object* v_pivot_1548_, lean_object* v_as_1549_, lean_object* v_i_1550_, lean_object* v_k_1551_, lean_object* v_ilo_1552_, lean_object* v_ik_1553_, lean_object* v_w_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_1544_, v_lo_1545_, v_hi_1546_, v_hhi_1547_, v_pivot_1548_, v_as_1549_, v_i_1550_, v_k_1551_, v_ilo_1552_, v_ik_1553_, v_w_1554_);
lean_dec_ref(v_pivot_1548_);
lean_dec(v_hi_1546_);
lean_dec(v_lo_1545_);
lean_dec(v_n_1544_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1556_, lean_object* v_i_1557_, lean_object* v_source_1558_, lean_object* v_target_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1557_, v_source_1558_, v_target_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1561_, lean_object* v_preNode_1562_, lean_object* v_postNode_1563_, lean_object* v___x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1562_, v_postNode_1563_, v___x_1564_, v_x_1565_, v_x_1566_, v___y_1567_, v___y_1568_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1571_, lean_object* v_preNode_1572_, lean_object* v_postNode_1573_, lean_object* v___x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1571_, v_preNode_1572_, v_postNode_1573_, v___x_1574_, v_x_1575_, v_x_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1581_, v___y_1583_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1592_, v_x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1597_ = l_Lean_Elab_Command_addLinter(v___x_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1599_;
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
