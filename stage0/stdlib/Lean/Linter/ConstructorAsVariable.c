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
uint8_t v___y_21688__boxed_219_; uint8_t v_suppressElabErrors_boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v___y_21688__boxed_219_ = lean_unbox(v___y_216_);
v_suppressElabErrors_boxed_220_ = lean_unbox(v_suppressElabErrors_217_);
v_res_221_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___lam__0(v___y_21688__boxed_219_, v_suppressElabErrors_boxed_220_, v_x_218_);
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
lean_dec_ref_known(v___x_228_, 1);
if (lean_obj_tag(v_val_230_) == 1)
{
uint8_t v_v_231_; 
v_v_231_ = lean_ctor_get_uint8(v_val_230_, 0);
lean_dec_ref_known(v_val_230_, 0);
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
lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; lean_object* v___y_289_; uint8_t v___y_290_; lean_object* v___y_291_; uint8_t v___y_347_; uint8_t v___y_348_; uint8_t v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; uint8_t v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; uint8_t v___y_378_; lean_object* v___y_379_; uint8_t v___y_383_; uint8_t v___y_384_; uint8_t v___y_385_; uint8_t v___x_400_; uint8_t v___y_402_; uint8_t v___y_403_; uint8_t v___y_404_; uint8_t v___y_406_; uint8_t v___x_418_; 
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
lean_dec_ref_known(v___x_292_, 1);
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
lean_ctor_set(v___x_317_, 1, v___y_287_);
lean_inc_ref(v___y_284_);
lean_inc_ref(v___y_286_);
v___x_318_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_318_, 0, v___y_286_);
lean_ctor_set(v___x_318_, 1, v___y_285_);
lean_ctor_set(v___x_318_, 2, v___y_289_);
lean_ctor_set(v___x_318_, 3, v___y_284_);
lean_ctor_set(v___x_318_, 4, v___x_317_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*5, v___y_288_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*5 + 1, v___y_290_);
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
lean_dec(v___y_289_);
lean_dec_ref(v___y_287_);
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
lean_dec(v___y_289_);
lean_dec_ref(v___y_287_);
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
v___x_361_ = l_Lean_FileMap_toPosition(v_fileMap_353_, v___y_350_);
lean_dec(v___y_350_);
v___x_362_ = l_Lean_FileMap_toPosition(v_fileMap_353_, v___y_351_);
lean_dec(v___y_351_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15___closed__0));
if (v_suppressElabErrors_354_ == 0)
{
lean_del_object(v___x_359_);
v___y_284_ = v___x_364_;
v___y_285_ = v___x_361_;
v___y_286_ = v_fileName_352_;
v___y_287_ = v_a_357_;
v___y_288_ = v___y_348_;
v___y_289_ = v___x_363_;
v___y_290_ = v___y_349_;
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
lean_dec_ref_known(v___x_363_, 1);
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
v___y_284_ = v___x_364_;
v___y_285_ = v___x_361_;
v___y_286_ = v_fileName_352_;
v___y_287_ = v_a_357_;
v___y_288_ = v___y_348_;
v___y_289_ = v___x_363_;
v___y_290_ = v___y_349_;
v___y_291_ = v___y_281_;
goto v___jp_283_;
}
}
}
}
v___jp_374_:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Syntax_getTailPos_x3f(v___y_376_, v___y_377_);
lean_dec(v___y_376_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_inc(v___y_379_);
v___y_347_ = v___y_375_;
v___y_348_ = v___y_377_;
v___y_349_ = v___y_378_;
v___y_350_ = v___y_379_;
v___y_351_ = v___y_379_;
goto v___jp_346_;
}
else
{
lean_object* v_val_381_; 
v_val_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_val_381_);
lean_dec_ref_known(v___x_380_, 1);
v___y_347_ = v___y_375_;
v___y_348_ = v___y_377_;
v___y_349_ = v___y_378_;
v___y_350_ = v___y_379_;
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
lean_dec_ref_known(v___x_386_, 1);
v_ref_388_ = l_Lean_replaceRef(v_ref_276_, v_a_387_);
lean_dec(v_a_387_);
v___x_389_ = l_Lean_Syntax_getPos_x3f(v_ref_388_, v___y_384_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_unsigned_to_nat(0u);
v___y_375_ = v___y_383_;
v___y_376_ = v_ref_388_;
v___y_377_ = v___y_384_;
v___y_378_ = v___y_385_;
v___y_379_ = v___x_390_;
goto v___jp_374_;
}
else
{
lean_object* v_val_391_; 
v_val_391_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_391_);
lean_dec_ref_known(v___x_389_, 1);
v___y_375_ = v___y_383_;
v___y_376_ = v_ref_388_;
v___y_377_ = v___y_384_;
v___y_378_ = v___y_385_;
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
lean_object* v_name_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_473_; 
v_name_456_ = lean_ctor_get(v_linterOption_450_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_linterOption_450_);
if (v_isSharedCheck_473_ == 0)
{
lean_object* v_unused_474_; 
v_unused_474_ = lean_ctor_get(v_linterOption_450_, 1);
lean_dec(v_unused_474_);
v___x_458_ = v_linterOption_450_;
v_isShared_459_ = v_isSharedCheck_473_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_name_456_);
lean_dec(v_linterOption_450_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_473_;
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
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_472_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v_disable_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_464_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___closed__3);
v___x_465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v_disable_466_ = l_Lean_MessageData_note(v___x_465_);
v___x_467_ = l_Lean_Linter_linterMessageTag;
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v_msg_452_);
lean_ctor_set(v___x_468_, 1, v_disable_466_);
v___x_469_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_467_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_470_, 0, v_name_456_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11(v_stx_451_, v___x_470_, v___y_453_, v___y_454_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* v_linterOption_475_, lean_object* v_stx_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v_linterOption_475_, v_stx_476_, v_msg_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v_stx_476_);
return v_res_481_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__0));
v___x_484_ = l_Lean_stringToMessageData(v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__2));
v___x_487_ = l_Lean_stringToMessageData(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__4));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__6));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__8));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__10));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_503_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_555_; 
v_a_509_ = lean_array_uget(v_as_500_, v_i_502_);
v_snd_510_ = lean_ctor_get(v_a_509_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_a_509_, 0);
lean_dec(v_unused_556_);
v___x_512_ = v_a_509_;
v_isShared_513_ = v_isSharedCheck_555_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_dec(v_a_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_555_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_snd_514_; lean_object* v_fst_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_554_; 
v_snd_514_ = lean_ctor_get(v_snd_510_, 1);
v_fst_515_ = lean_ctor_get(v_snd_510_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_snd_510_);
if (v_isSharedCheck_554_ == 0)
{
v___x_517_ = v_snd_510_;
v_isShared_518_ = v_isSharedCheck_554_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_snd_514_);
lean_inc(v_fst_515_);
lean_dec(v_snd_510_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_554_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_553_; 
v_fst_519_ = lean_ctor_get(v_snd_514_, 0);
v_snd_520_ = lean_ctor_get(v_snd_514_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_snd_514_);
if (v_isSharedCheck_553_ == 0)
{
v___x_522_ = v_snd_514_;
v_isShared_523_ = v_isSharedCheck_553_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_inc(v_fst_519_);
lean_dec(v_snd_514_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_553_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_524_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_525_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__1);
v___x_526_ = l_Lean_MessageData_ofName(v_fst_519_);
lean_inc_ref(v___x_526_);
if (v_isShared_523_ == 0)
{
lean_ctor_set_tag(v___x_522_, 7);
lean_ctor_set(v___x_522_, 1, v___x_526_);
lean_ctor_set(v___x_522_, 0, v___x_525_);
v___x_528_ = v___x_522_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_552_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__3);
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 7);
lean_ctor_set(v___x_517_, 1, v___x_529_);
lean_ctor_set(v___x_517_, 0, v___x_528_);
v___x_531_ = v___x_517_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_551_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = l_Lean_MessageData_ofName(v_snd_520_);
lean_inc_ref(v___x_532_);
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 7);
lean_ctor_set(v___x_512_, 1, v___x_532_);
lean_ctor_set(v___x_512_, 0, v___x_531_);
v___x_534_ = v___x_512_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_532_);
v___x_534_ = v_reuseFailAlloc_550_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__5);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__7);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_526_);
v___x_539_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__9);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_532_);
v___x_542_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___closed__11);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_536_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7(v___x_524_, v_fst_515_, v___x_544_, v___y_504_, v___y_505_);
lean_dec(v_fst_515_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; size_t v___x_547_; size_t v___x_548_; 
lean_dec_ref_known(v___x_545_, 1);
v___x_546_ = lean_box(0);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_502_, v___x_547_);
v_i_502_ = v___x_548_;
v_b_503_ = v___x_546_;
goto _start;
}
else
{
return v___x_545_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* v_as_557_, lean_object* v_sz_558_, lean_object* v_i_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
size_t v_sz_boxed_564_; size_t v_i_boxed_565_; lean_object* v_res_566_; 
v_sz_boxed_564_ = lean_unbox_usize(v_sz_558_);
lean_dec(v_sz_558_);
v_i_boxed_565_ = lean_unbox_usize(v_i_559_);
lean_dec(v_i_559_);
v_res_566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v_as_557_, v_sz_boxed_564_, v_i_boxed_565_, v_b_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v_as_557_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(uint8_t v___x_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(v___x_567_);
v___x_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed(lean_object* v___x_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
uint8_t v___x_22304__boxed_583_; lean_object* v_res_584_; 
v___x_22304__boxed_583_ = lean_unbox(v___x_576_);
v_res_584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0(v___x_22304__boxed_583_, v_x_577_, v_x_578_, v_x_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v_x_579_);
lean_dec_ref(v_x_578_);
lean_dec_ref(v_x_577_);
return v_res_584_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
uint8_t v___x_587_; 
v___x_587_ = 0;
return v___x_587_;
}
else
{
lean_object* v_key_588_; lean_object* v_tail_589_; uint8_t v___x_590_; 
v_key_588_ = lean_ctor_get(v_x_586_, 0);
v_tail_589_ = lean_ctor_get(v_x_586_, 2);
v___x_590_ = l_Lean_Syntax_instBEqRange_beq(v_key_588_, v_a_585_);
if (v___x_590_ == 0)
{
v_x_586_ = v_tail_589_;
goto _start;
}
else
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg___boxed(lean_object* v_a_592_, lean_object* v_x_593_){
_start:
{
uint8_t v_res_594_; lean_object* v_r_595_; 
v_res_594_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_592_, v_x_593_);
lean_dec(v_x_593_);
lean_dec_ref(v_a_592_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(lean_object* v_m_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_buckets_598_; lean_object* v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v_fold_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_buckets_598_ = lean_ctor_get(v_m_596_, 1);
v___x_599_ = lean_array_get_size(v_buckets_598_);
v___x_600_ = l_Lean_Syntax_instHashableRange_hash(v_a_597_);
v___x_601_ = 32ULL;
v___x_602_ = lean_uint64_shift_right(v___x_600_, v___x_601_);
v_fold_603_ = lean_uint64_xor(v___x_600_, v___x_602_);
v___x_604_ = 16ULL;
v___x_605_ = lean_uint64_shift_right(v_fold_603_, v___x_604_);
v___x_606_ = lean_uint64_xor(v_fold_603_, v___x_605_);
v___x_607_ = lean_uint64_to_usize(v___x_606_);
v___x_608_ = lean_usize_of_nat(v___x_599_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v___x_608_, v___x_609_);
v___x_611_ = lean_usize_land(v___x_607_, v___x_610_);
v___x_612_ = lean_array_uget_borrowed(v_buckets_598_, v___x_611_);
v___x_613_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_597_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg___boxed(lean_object* v_m_614_, lean_object* v_a_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_614_, v_a_615_);
lean_dec_ref(v_a_615_);
lean_dec_ref(v_m_614_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_x_620_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
lean_dec(v_b_619_);
lean_dec_ref(v_a_618_);
return v_x_620_;
}
else
{
lean_object* v_key_621_; lean_object* v_value_622_; lean_object* v_tail_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_635_; 
v_key_621_ = lean_ctor_get(v_x_620_, 0);
v_value_622_ = lean_ctor_get(v_x_620_, 1);
v_tail_623_ = lean_ctor_get(v_x_620_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_620_);
if (v_isSharedCheck_635_ == 0)
{
v___x_625_ = v_x_620_;
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tail_623_);
lean_inc(v_value_622_);
lean_inc(v_key_621_);
lean_dec(v_x_620_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_635_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_Syntax_instBEqRange_beq(v_key_621_, v_a_618_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_628_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_618_, v_b_619_, v_tail_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 2, v___x_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_key_621_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_value_622_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
else
{
lean_object* v___x_633_; 
lean_dec(v_value_622_);
lean_dec(v_key_621_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v_b_619_);
lean_ctor_set(v___x_625_, 0, v_a_618_);
v___x_633_ = v___x_625_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_618_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_b_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_tail_623_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
return v_x_636_;
}
else
{
lean_object* v_key_638_; lean_object* v_value_639_; lean_object* v_tail_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_663_; 
v_key_638_ = lean_ctor_get(v_x_637_, 0);
v_value_639_ = lean_ctor_get(v_x_637_, 1);
v_tail_640_ = lean_ctor_get(v_x_637_, 2);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_663_ == 0)
{
v___x_642_ = v_x_637_;
v_isShared_643_ = v_isSharedCheck_663_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_tail_640_);
lean_inc(v_value_639_);
lean_inc(v_key_638_);
lean_dec(v_x_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_663_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v___x_647_; uint64_t v_fold_648_; uint64_t v___x_649_; uint64_t v___x_650_; uint64_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_644_ = lean_array_get_size(v_x_636_);
v___x_645_ = l_Lean_Syntax_instHashableRange_hash(v_key_638_);
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
v___x_657_ = lean_array_uget_borrowed(v_x_636_, v___x_656_);
lean_inc(v___x_657_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 2, v___x_657_);
v___x_659_ = v___x_642_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_key_638_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_value_639_);
lean_ctor_set(v_reuseFailAlloc_662_, 2, v___x_657_);
v___x_659_ = v_reuseFailAlloc_662_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v___x_660_; 
v___x_660_ = lean_array_uset(v_x_636_, v___x_656_, v___x_659_);
v_x_636_ = v___x_660_;
v_x_637_ = v_tail_640_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(lean_object* v_i_664_, lean_object* v_source_665_, lean_object* v_target_666_){
_start:
{
lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_667_ = lean_array_get_size(v_source_665_);
v___x_668_ = lean_nat_dec_lt(v_i_664_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec_ref(v_source_665_);
lean_dec(v_i_664_);
return v_target_666_;
}
else
{
lean_object* v_es_669_; lean_object* v___x_670_; lean_object* v_source_671_; lean_object* v_target_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_es_669_ = lean_array_fget(v_source_665_, v_i_664_);
v___x_670_ = lean_box(0);
v_source_671_ = lean_array_fset(v_source_665_, v_i_664_, v___x_670_);
v_target_672_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_target_666_, v_es_669_);
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = lean_nat_add(v_i_664_, v___x_673_);
lean_dec(v_i_664_);
v_i_664_ = v___x_674_;
v_source_665_ = v_source_671_;
v_target_666_ = v_target_672_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(lean_object* v_data_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_nbuckets_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_677_ = lean_array_get_size(v_data_676_);
v___x_678_ = lean_unsigned_to_nat(2u);
v_nbuckets_679_ = lean_nat_mul(v___x_677_, v___x_678_);
v___x_680_ = lean_unsigned_to_nat(0u);
v___x_681_ = lean_box(0);
v___x_682_ = lean_mk_array(v_nbuckets_679_, v___x_681_);
v___x_683_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v___x_680_, v_data_676_, v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* v_m_684_, lean_object* v_a_685_, lean_object* v_b_686_){
_start:
{
lean_object* v_size_687_; lean_object* v_buckets_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_731_; 
v_size_687_ = lean_ctor_get(v_m_684_, 0);
v_buckets_688_ = lean_ctor_get(v_m_684_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_m_684_);
if (v_isSharedCheck_731_ == 0)
{
v___x_690_ = v_m_684_;
v_isShared_691_ = v_isSharedCheck_731_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_buckets_688_);
lean_inc(v_size_687_);
lean_dec(v_m_684_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_731_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; uint64_t v___x_693_; uint64_t v___x_694_; uint64_t v___x_695_; uint64_t v_fold_696_; uint64_t v___x_697_; uint64_t v___x_698_; uint64_t v___x_699_; size_t v___x_700_; size_t v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; lean_object* v_bkt_705_; uint8_t v___x_706_; 
v___x_692_ = lean_array_get_size(v_buckets_688_);
v___x_693_ = l_Lean_Syntax_instHashableRange_hash(v_a_685_);
v___x_694_ = 32ULL;
v___x_695_ = lean_uint64_shift_right(v___x_693_, v___x_694_);
v_fold_696_ = lean_uint64_xor(v___x_693_, v___x_695_);
v___x_697_ = 16ULL;
v___x_698_ = lean_uint64_shift_right(v_fold_696_, v___x_697_);
v___x_699_ = lean_uint64_xor(v_fold_696_, v___x_698_);
v___x_700_ = lean_uint64_to_usize(v___x_699_);
v___x_701_ = lean_usize_of_nat(v___x_692_);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_sub(v___x_701_, v___x_702_);
v___x_704_ = lean_usize_land(v___x_700_, v___x_703_);
v_bkt_705_ = lean_array_uget_borrowed(v_buckets_688_, v___x_704_);
v___x_706_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_685_, v_bkt_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v_size_x27_708_; lean_object* v___x_709_; lean_object* v_buckets_x27_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v_size_x27_708_ = lean_nat_add(v_size_687_, v___x_707_);
lean_dec(v_size_687_);
lean_inc(v_bkt_705_);
v___x_709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_709_, 0, v_a_685_);
lean_ctor_set(v___x_709_, 1, v_b_686_);
lean_ctor_set(v___x_709_, 2, v_bkt_705_);
v_buckets_x27_710_ = lean_array_uset(v_buckets_688_, v___x_704_, v___x_709_);
v___x_711_ = lean_unsigned_to_nat(4u);
v___x_712_ = lean_nat_mul(v_size_x27_708_, v___x_711_);
v___x_713_ = lean_unsigned_to_nat(3u);
v___x_714_ = lean_nat_div(v___x_712_, v___x_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_array_get_size(v_buckets_x27_710_);
v___x_716_ = lean_nat_dec_le(v___x_714_, v___x_715_);
lean_dec(v___x_714_);
if (v___x_716_ == 0)
{
lean_object* v_val_717_; lean_object* v___x_719_; 
v_val_717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_buckets_x27_710_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_val_717_);
lean_ctor_set(v___x_690_, 0, v_size_x27_708_);
v___x_719_ = v___x_690_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_size_x27_708_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_val_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
else
{
lean_object* v___x_722_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_buckets_x27_710_);
lean_ctor_set(v___x_690_, 0, v_size_x27_708_);
v___x_722_ = v___x_690_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_size_x27_708_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_buckets_x27_710_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
lean_object* v___x_724_; lean_object* v_buckets_x27_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
lean_inc(v_bkt_705_);
v___x_724_ = lean_box(0);
v_buckets_x27_725_ = lean_array_uset(v_buckets_688_, v___x_704_, v___x_724_);
v___x_726_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_685_, v_b_686_, v_bkt_705_);
v___x_727_ = lean_array_uset(v_buckets_x27_725_, v___x_704_, v___x_726_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v___x_727_);
v___x_729_ = v___x_690_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_size_687_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(lean_object* v_str_732_, lean_object* v_val_733_, lean_object* v_info_734_, lean_object* v___x_735_, lean_object* v_val_736_, uint8_t v___x_737_, lean_object* v_as_x27_738_, lean_object* v_b_739_, lean_object* v___y_740_){
_start:
{
if (lean_obj_tag(v_as_x27_738_) == 0)
{
lean_object* v___x_742_; 
lean_dec_ref(v_val_736_);
lean_dec(v___x_735_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v_b_739_);
return v___x_742_;
}
else
{
lean_object* v_head_743_; lean_object* v_tail_744_; lean_object* v___x_745_; lean_object* v_env_746_; lean_object* v___x_747_; lean_object* v___x_760_; 
v_head_743_ = lean_ctor_get(v_as_x27_738_, 0);
v_tail_744_ = lean_ctor_get(v_as_x27_738_, 1);
v___x_745_ = lean_st_ref_get(v___y_740_);
v_env_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc_ref(v_env_746_);
lean_dec(v___x_745_);
v___x_747_ = lean_box(0);
lean_inc(v_head_743_);
v___x_760_ = l_Lean_Environment_find_x3f(v_env_746_, v_head_743_, v___x_737_);
if (lean_obj_tag(v___x_760_) == 1)
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_760_, 1);
if (lean_obj_tag(v_val_761_) == 6)
{
lean_object* v_val_762_; lean_object* v_numFields_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_val_762_ = lean_ctor_get(v_val_761_, 0);
lean_inc_ref(v_val_762_);
lean_dec_ref_known(v_val_761_, 1);
v_numFields_763_ = lean_ctor_get(v_val_762_, 4);
lean_inc(v_numFields_763_);
lean_dec_ref(v_val_762_);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_nat_dec_lt(v___x_764_, v_numFields_763_);
lean_dec(v_numFields_763_);
if (v___x_765_ == 0)
{
goto v___jp_748_;
}
else
{
v_as_x27_738_ = v_tail_744_;
v_b_739_ = v___x_747_;
goto _start;
}
}
else
{
lean_dec(v_val_761_);
goto v___jp_748_;
}
}
else
{
lean_dec(v___x_760_);
goto v___jp_748_;
}
v___jp_748_:
{
if (lean_obj_tag(v_head_743_) == 1)
{
lean_object* v_str_749_; uint8_t v___x_750_; 
v_str_749_ = lean_ctor_get(v_head_743_, 1);
v___x_750_ = lean_string_dec_eq(v_str_749_, v_str_732_);
if (v___x_750_ == 0)
{
v_as_x27_738_ = v_tail_744_;
v_b_739_ = v___x_747_;
goto _start;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_752_ = lean_st_ref_take(v_val_733_);
v___x_753_ = l_Lean_Elab_Info_stx(v_info_734_);
lean_inc_ref(v_head_743_);
lean_inc(v___x_735_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_735_);
lean_ctor_set(v___x_754_, 1, v_head_743_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
lean_inc_ref(v_val_736_);
v___x_756_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v___x_752_, v_val_736_, v___x_755_);
v___x_757_ = lean_st_ref_set(v_val_733_, v___x_756_);
v_as_x27_738_ = v_tail_744_;
v_b_739_ = v___x_747_;
goto _start;
}
}
else
{
v_as_x27_738_ = v_tail_744_;
v_b_739_ = v___x_747_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg___boxed(lean_object* v_str_767_, lean_object* v_val_768_, lean_object* v_info_769_, lean_object* v___x_770_, lean_object* v_val_771_, lean_object* v___x_772_, lean_object* v_as_x27_773_, lean_object* v_b_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
uint8_t v___x_22568__boxed_777_; lean_object* v_res_778_; 
v___x_22568__boxed_777_ = lean_unbox(v___x_772_);
v_res_778_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_767_, v_val_768_, v_info_769_, v___x_770_, v_val_771_, v___x_22568__boxed_777_, v_as_x27_773_, v_b_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec(v_as_x27_773_);
lean_dec_ref(v_info_769_);
lean_dec(v_val_768_);
lean_dec_ref(v_str_767_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(lean_object* v_ty_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(v_ty_779_, v___y_781_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = lean_whnf(v_a_786_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_787_;
}
else
{
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed(lean_object* v_ty_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1(v_ty_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(lean_object* v_val_795_, lean_object* v___x_796_, lean_object* v_val_797_, lean_object* v___x_798_, lean_object* v_ci_799_, lean_object* v_info_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
if (lean_obj_tag(v_info_800_) == 1)
{
lean_object* v_i_805_; lean_object* v_expr_806_; 
v_i_805_ = lean_ctor_get(v_info_800_, 0);
v_expr_806_ = lean_ctor_get(v_i_805_, 3);
if (lean_obj_tag(v_expr_806_) == 1)
{
lean_object* v_lctx_807_; lean_object* v_expectedType_x3f_808_; uint8_t v_isBinder_809_; lean_object* v_fvarId_810_; lean_object* v___x_811_; 
v_lctx_807_ = lean_ctor_get(v_i_805_, 1);
v_expectedType_x3f_808_ = lean_ctor_get(v_i_805_, 2);
v_isBinder_809_ = lean_ctor_get_uint8(v_i_805_, sizeof(void*)*4);
v_fvarId_810_ = lean_ctor_get(v_expr_806_, 0);
v___x_811_ = l_Lean_Elab_Info_range_x3f(v_info_800_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_967_; 
v_val_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_967_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_967_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_val_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_967_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_st_ref_get(v_val_795_);
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v___x_816_, v_val_812_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = l_Lean_Elab_Info_stx(v_info_800_);
v___x_819_ = l_Lean_Syntax_getHeadInfo(v___x_818_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_dec_ref_known(v___x_819_, 4);
if (v_isBinder_809_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v___x_818_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_796_);
v___x_821_ = v___x_814_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_796_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_823_; 
lean_inc(v_fvarId_810_);
lean_inc_ref(v_lctx_807_);
v___x_823_ = lean_local_ctx_find(v_lctx_807_, v_fvarId_810_);
if (lean_obj_tag(v___x_823_) == 1)
{
lean_object* v_val_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_957_; 
v_val_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_957_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_957_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_val_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_957_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_start_828_; uint8_t v___x_829_; 
v_start_828_ = lean_ctor_get(v_val_812_, 0);
v___x_829_ = l_Lean_Syntax_Range_contains(v_val_797_, v_start_828_, v___x_817_);
if (v___x_829_ == 0)
{
lean_object* v___x_831_; 
lean_dec(v_val_824_);
lean_dec(v___x_818_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_796_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_796_);
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
if (v___x_817_ == 0)
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = l_Lean_LocalDecl_userName(v_val_824_);
lean_dec(v_val_824_);
v___x_834_ = l_Lean_Name_hasMacroScopes(v___x_833_);
lean_dec(v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v_toCommandContextInfo_835_; lean_object* v_options_836_; lean_object* v___x_837_; 
v_toCommandContextInfo_835_ = lean_ctor_get(v_ci_799_, 0);
v_options_836_ = lean_ctor_get(v_toCommandContextInfo_835_, 4);
lean_inc_ref(v_options_836_);
v___x_837_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_options_836_, v___y_803_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_942_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_942_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_942_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_942_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_Linter_getLinterValue(v___x_798_, v_a_838_);
lean_dec(v_a_838_);
if (v___x_842_ == 0)
{
lean_object* v___x_844_; 
lean_del_object(v___x_826_);
lean_dec(v___x_818_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_796_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_796_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Syntax_getId(v___x_818_);
lean_dec(v___x_818_);
if (lean_obj_tag(v___x_846_) == 1)
{
lean_object* v_pre_847_; lean_object* v_str_848_; lean_object* v_ty_850_; lean_object* v___y_851_; lean_object* v___y_852_; 
v_pre_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_pre_847_);
v_str_848_ = lean_ctor_get(v___x_846_, 1);
lean_inc_ref(v_str_848_);
if (lean_obj_tag(v_pre_847_) == 0)
{
lean_del_object(v___x_840_);
if (lean_obj_tag(v_expectedType_x3f_808_) == 1)
{
lean_object* v_val_909_; 
lean_del_object(v___x_814_);
v_val_909_ = lean_ctor_get(v_expectedType_x3f_808_, 0);
lean_inc(v_val_909_);
v_ty_850_ = v_val_909_;
v___y_851_ = v___y_802_;
v___y_852_ = v___y_803_;
goto v___jp_849_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
lean_inc_ref(v_expr_806_);
v___x_910_ = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(v___x_910_, 0, v_expr_806_);
lean_inc_ref(v_ci_799_);
lean_inc_ref(v_i_805_);
v___x_911_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_805_, v_ci_799_, v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; 
lean_del_object(v___x_814_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v_ty_850_ = v_a_912_;
v___y_851_ = v___y_802_;
v___y_852_ = v___y_803_;
goto v___jp_849_;
}
else
{
lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_str_848_);
lean_dec_ref_known(v___x_846_, 2);
lean_del_object(v___x_826_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_val_812_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_934_ = lean_ctor_get(v_val_812_, 1);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_val_812_, 0);
lean_dec(v_unused_935_);
v___x_914_ = v_val_812_;
v_isShared_915_ = v_isSharedCheck_933_;
goto v_resetjp_913_;
}
else
{
lean_dec(v_val_812_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_933_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_932_; 
v_a_916_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_932_ == 0)
{
v___x_918_ = v___x_911_;
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_911_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_932_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_ref_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v_ref_920_ = lean_ctor_get(v___y_802_, 7);
v___x_921_ = lean_io_error_to_string(v_a_916_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 3);
lean_ctor_set(v___x_814_, 0, v___x_921_);
v___x_923_ = v___x_814_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_931_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l_Lean_MessageData_ofFormat(v___x_923_);
lean_inc(v_ref_920_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___x_924_);
lean_ctor_set(v___x_914_, 0, v_ref_920_);
v___x_926_ = v___x_914_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_ref_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_926_);
v___x_928_ = v___x_918_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
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
lean_object* v___x_937_; 
lean_dec_ref(v_str_848_);
lean_dec(v_pre_847_);
lean_dec_ref_known(v___x_846_, 2);
lean_del_object(v___x_826_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_796_);
v___x_937_ = v___x_840_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_796_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
v___jp_849_:
{
lean_object* v___f_853_; lean_object* v___x_854_; 
v___f_853_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__1___boxed), 6, 1);
lean_closure_set(v___f_853_, 0, v_ty_850_);
lean_inc_ref(v_i_805_);
v___x_854_ = l_Lean_Elab_TermInfo_runMetaM___redArg(v_i_805_, v_ci_799_, v___f_853_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_826_);
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_885_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_885_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_885_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Expr_getAppFn_x27(v_a_855_);
lean_dec(v_a_855_);
if (lean_obj_tag(v___x_859_) == 4)
{
lean_object* v_declName_860_; lean_object* v___x_861_; lean_object* v_env_862_; lean_object* v___x_863_; 
v_declName_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_declName_860_);
lean_dec_ref_known(v___x_859_, 2);
v___x_861_ = lean_st_ref_get(v___y_852_);
v_env_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc_ref(v_env_862_);
lean_dec(v___x_861_);
v___x_863_ = l_Lean_Environment_find_x3f(v_env_862_, v_declName_860_, v___x_817_);
if (lean_obj_tag(v___x_863_) == 1)
{
lean_object* v_val_864_; 
v_val_864_ = lean_ctor_get(v___x_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___x_863_, 1);
if (lean_obj_tag(v_val_864_) == 5)
{
lean_object* v_val_865_; lean_object* v_ctors_866_; lean_object* v___x_867_; 
lean_del_object(v___x_857_);
v_val_865_ = lean_ctor_get(v_val_864_, 0);
lean_inc_ref(v_val_865_);
lean_dec_ref_known(v_val_864_, 1);
v_ctors_866_ = lean_ctor_get(v_val_865_, 4);
lean_inc(v_ctors_866_);
lean_dec_ref(v_val_865_);
v___x_867_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_848_, v_val_795_, v_info_800_, v___x_846_, v_val_812_, v___x_817_, v_ctors_866_, v___x_796_, v___y_852_);
lean_dec(v_ctors_866_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_str_848_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_875_);
v___x_869_ = v___x_867_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_dec(v___x_867_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v___x_796_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_796_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
return v___x_867_;
}
}
else
{
lean_object* v___x_877_; 
lean_dec(v_val_864_);
lean_dec_ref(v_str_848_);
lean_dec_ref_known(v___x_846_, 2);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_796_);
v___x_877_ = v___x_857_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_796_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
else
{
lean_object* v___x_880_; 
lean_dec(v___x_863_);
lean_dec_ref(v_str_848_);
lean_dec_ref_known(v___x_846_, 2);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_796_);
v___x_880_ = v___x_857_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_796_);
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
lean_object* v___x_883_; 
lean_dec_ref(v___x_859_);
lean_dec_ref(v_str_848_);
lean_dec_ref_known(v___x_846_, 2);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_796_);
v___x_883_ = v___x_857_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_796_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_906_; 
lean_dec_ref(v_str_848_);
lean_dec_ref_known(v___x_846_, 2);
lean_dec_ref_known(v_info_800_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_val_812_);
if (v_isSharedCheck_906_ == 0)
{
lean_object* v_unused_907_; lean_object* v_unused_908_; 
v_unused_907_ = lean_ctor_get(v_val_812_, 1);
lean_dec(v_unused_907_);
v_unused_908_ = lean_ctor_get(v_val_812_, 0);
lean_dec(v_unused_908_);
v___x_887_ = v_val_812_;
v_isShared_888_ = v_isSharedCheck_906_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_val_812_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_906_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_905_; 
v_a_889_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_905_ == 0)
{
v___x_891_ = v___x_854_;
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_854_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_905_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_ref_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_ref_893_ = lean_ctor_get(v___y_851_, 7);
v___x_894_ = lean_io_error_to_string(v_a_889_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 3);
lean_ctor_set(v___x_826_, 0, v___x_894_);
v___x_896_ = v___x_826_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_904_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = l_Lean_MessageData_ofFormat(v___x_896_);
lean_inc(v_ref_893_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_897_);
lean_ctor_set(v___x_887_, 0, v_ref_893_);
v___x_899_ = v___x_887_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_ref_893_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_899_);
v___x_901_ = v___x_891_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
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
lean_object* v___x_940_; 
lean_dec(v___x_846_);
lean_del_object(v___x_826_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_796_);
v___x_940_ = v___x_840_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_796_);
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
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_del_object(v___x_826_);
lean_dec(v___x_818_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
v_a_943_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_837_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_837_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
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
else
{
lean_object* v___x_952_; 
lean_dec(v___x_818_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_796_);
v___x_952_ = v___x_826_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_796_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_object* v___x_955_; 
lean_dec(v_val_824_);
lean_dec(v___x_818_);
lean_del_object(v___x_814_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_796_);
v___x_955_ = v___x_826_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_796_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
else
{
lean_object* v___x_959_; 
lean_dec(v___x_823_);
lean_dec(v___x_818_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_796_);
v___x_959_ = v___x_814_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_796_);
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
else
{
lean_object* v___x_962_; 
lean_dec(v___x_819_);
lean_dec(v___x_818_);
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_796_);
v___x_962_ = v___x_814_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_796_);
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
lean_dec(v_val_812_);
lean_dec_ref_known(v_info_800_, 1);
lean_dec_ref(v_ci_799_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_796_);
v___x_965_ = v___x_814_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_796_);
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
else
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v___x_811_);
lean_dec_ref(v_ci_799_);
v_isSharedCheck_974_ = !lean_is_exclusive(v_info_800_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_info_800_, 0);
lean_dec(v_unused_975_);
v___x_969_ = v_info_800_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_dec(v_info_800_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 0);
lean_ctor_set(v___x_969_, 0, v___x_796_);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_796_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
else
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v_ci_799_);
v_isSharedCheck_982_ = !lean_is_exclusive(v_info_800_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_info_800_, 0);
lean_dec(v_unused_983_);
v___x_977_ = v_info_800_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_dec(v_info_800_);
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
lean_ctor_set(v___x_977_, 0, v___x_796_);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_796_);
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
lean_object* v___x_984_; 
lean_dec_ref(v_info_800_);
lean_dec_ref(v_ci_799_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_796_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed(lean_object* v_val_985_, lean_object* v___x_986_, lean_object* v_val_987_, lean_object* v___x_988_, lean_object* v_ci_989_, lean_object* v_info_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2(v_val_985_, v___x_986_, v_val_987_, v___x_988_, v_ci_989_, v_info_990_, v_x_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec_ref(v_x_991_);
lean_dec_ref(v___x_988_);
lean_dec_ref(v_val_987_);
lean_dec(v_val_985_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(lean_object* v_postNode_996_, lean_object* v_ci_997_, lean_object* v_i_998_, lean_object* v_cs_999_, lean_object* v_x_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
lean_inc(v___y_1002_);
lean_inc_ref(v___y_1001_);
v___x_1004_ = lean_apply_6(v_postNode_996_, v_ci_997_, v_i_998_, v_cs_999_, v___y_1001_, v___y_1002_, lean_box(0));
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed(lean_object* v_postNode_1005_, lean_object* v_ci_1006_, lean_object* v_i_1007_, lean_object* v_cs_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0(v_postNode_1005_, v_ci_1006_, v_i_1007_, v_cs_1008_, v_x_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v_x_1009_);
return v_res_1013_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_instMonadEIO(lean_box(0));
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_toApplicative_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1054_; 
v___x_1021_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__0);
v___x_1022_ = l_StateRefT_x27_instMonad___redArg(v___x_1021_);
v_toApplicative_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1022_, 1);
lean_dec(v_unused_1055_);
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1054_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_toApplicative_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1054_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_toFunctor_1027_; lean_object* v_toSeq_1028_; lean_object* v_toSeqLeft_1029_; lean_object* v_toSeqRight_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1052_; 
v_toFunctor_1027_ = lean_ctor_get(v_toApplicative_1023_, 0);
v_toSeq_1028_ = lean_ctor_get(v_toApplicative_1023_, 2);
v_toSeqLeft_1029_ = lean_ctor_get(v_toApplicative_1023_, 3);
v_toSeqRight_1030_ = lean_ctor_get(v_toApplicative_1023_, 4);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_toApplicative_1023_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_toApplicative_1023_, 1);
lean_dec(v_unused_1053_);
v___x_1032_ = v_toApplicative_1023_;
v_isShared_1033_ = v_isSharedCheck_1052_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_toSeqRight_1030_);
lean_inc(v_toSeqLeft_1029_);
lean_inc(v_toSeq_1028_);
lean_inc(v_toFunctor_1027_);
lean_dec(v_toApplicative_1023_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1052_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1043_; 
v___f_1034_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__1));
v___f_1035_ = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___closed__2));
lean_inc_ref(v_toFunctor_1027_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toFunctor_1027_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toFunctor_1027_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___f_1036_);
lean_ctor_set(v___x_1038_, 1, v___f_1037_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeqRight_1030_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeqLeft_1029_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeq_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 4, v___f_1039_);
lean_ctor_set(v___x_1032_, 3, v___f_1040_);
lean_ctor_set(v___x_1032_, 2, v___f_1041_);
lean_ctor_set(v___x_1032_, 1, v___f_1034_);
lean_ctor_set(v___x_1032_, 0, v___x_1038_);
v___x_1043_ = v___x_1032_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___f_1034_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v___f_1041_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v___f_1039_);
v___x_1043_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___f_1035_);
lean_ctor_set(v___x_1025_, 0, v___x_1043_);
v___x_1045_ = v___x_1025_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___f_1035_);
v___x_1045_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_18811__overap_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = l_instInhabitedOfMonad___redArg(v___x_1045_, v___x_1046_);
v___x_18811__overap_1048_ = lean_panic_fn_borrowed(v___x_1047_, v_msg_1017_);
lean_dec(v___x_1047_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
v___x_1049_ = lean_apply_3(v___x_18811__overap_1048_, v___y_1018_, v___y_1019_, lean_box(0));
return v___x_1049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1060_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1064_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__2));
v___x_1065_ = lean_unsigned_to_nat(21u);
v___x_1066_ = lean_unsigned_to_nat(65u);
v___x_1067_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__1));
v___x_1068_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__0));
v___x_1069_ = l_mkPanicMessageWithDecl(v___x_1068_, v___x_1067_, v___x_1066_, v___x_1065_, v___x_1064_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(lean_object* v_preNode_1070_, lean_object* v_postNode_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
switch(lean_obj_tag(v_x_1073_))
{
case 0:
{
lean_object* v_i_1077_; lean_object* v_t_1078_; lean_object* v___x_1079_; 
v_i_1077_ = lean_ctor_get(v_x_1073_, 0);
lean_inc_ref(v_i_1077_);
v_t_1078_ = lean_ctor_get(v_x_1073_, 1);
lean_inc_ref(v_t_1078_);
lean_dec_ref_known(v_x_1073_, 2);
v___x_1079_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_1077_, v_x_1072_);
v_x_1072_ = v___x_1079_;
v_x_1073_ = v_t_1078_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref_known(v_x_1073_, 2);
lean_dec_ref(v_postNode_1071_);
lean_dec_ref(v_preNode_1070_);
v___x_1081_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___closed__3);
v___x_1082_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v___x_1081_, v___y_1074_, v___y_1075_);
return v___x_1082_;
}
else
{
lean_object* v_i_1083_; lean_object* v_children_1084_; lean_object* v_val_1085_; lean_object* v___x_1086_; 
v_i_1083_ = lean_ctor_get(v_x_1073_, 0);
lean_inc_ref_n(v_i_1083_, 2);
v_children_1084_ = lean_ctor_get(v_x_1073_, 1);
lean_inc_ref_n(v_children_1084_, 2);
lean_dec_ref_known(v_x_1073_, 2);
v_val_1085_ = lean_ctor_get(v_x_1072_, 0);
lean_inc_n(v_val_1085_, 2);
lean_inc_ref(v_preNode_1070_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1086_ = lean_apply_6(v_preNode_1070_, v_val_1085_, v_i_1083_, v_children_1084_, v___y_1074_, v___y_1075_, lean_box(0));
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; uint8_t v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = lean_unbox(v_a_1087_);
lean_dec(v_a_1087_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v_preNode_1070_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v_x_1072_, 0);
lean_dec(v_unused_1114_);
v___x_1090_ = v_x_1072_;
v_isShared_1091_ = v_isSharedCheck_1113_;
goto v_resetjp_1089_;
}
else
{
lean_dec(v_x_1072_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1113_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box(0);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1093_ = lean_apply_7(v_postNode_1071_, v_val_1085_, v_i_1083_, v_children_1084_, v___x_1092_, v___y_1074_, v___y_1075_, lean_box(0));
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1104_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_a_1094_);
v___x_1099_ = v___x_1090_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1101_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1099_);
v___x_1101_ = v___x_1096_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
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
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_del_object(v___x_1090_);
v_a_1105_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1093_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1093_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
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
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = l_Lean_Elab_Info_updateContext_x3f(v_x_1072_, v_i_1083_);
v___x_1116_ = l_Lean_PersistentArray_toList___redArg(v_children_1084_);
v___x_1117_ = lean_box(0);
lean_inc_ref(v_postNode_1071_);
v___x_1118_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1070_, v_postNode_1071_, v___x_1115_, v___x_1116_, v___x_1117_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1120_ = lean_apply_7(v_postNode_1071_, v_val_1085_, v_i_1083_, v_children_1084_, v_a_1119_, v___y_1074_, v___y_1075_, lean_box(0));
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_a_1130_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1120_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1120_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v_val_1085_);
lean_dec_ref(v_children_1084_);
lean_dec_ref(v_i_1083_);
lean_dec_ref(v_postNode_1071_);
v_a_1138_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1118_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1118_);
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
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_val_1085_);
lean_dec_ref(v_children_1084_);
lean_dec_ref_known(v_x_1072_, 1);
lean_dec_ref(v_i_1083_);
lean_dec_ref(v_postNode_1071_);
lean_dec_ref(v_preNode_1070_);
v_a_1146_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1086_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1086_);
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
default: 
{
lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_x_1072_);
lean_dec_ref(v_postNode_1071_);
lean_dec_ref(v_preNode_1070_);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_x_1073_);
if (v_isSharedCheck_1161_ == 0)
{
lean_object* v_unused_1162_; 
v_unused_1162_ = lean_ctor_get(v_x_1073_, 0);
lean_dec(v_unused_1162_);
v___x_1155_ = v_x_1073_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_dec(v_x_1073_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_box(0);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
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
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(lean_object* v_preNode_1163_, lean_object* v_postNode_1164_, lean_object* v___x_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
if (lean_obj_tag(v_x_1166_) == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec(v___x_1165_);
lean_dec_ref(v_postNode_1164_);
lean_dec_ref(v_preNode_1163_);
v___x_1171_ = l_List_reverse___redArg(v_x_1167_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
else
{
lean_object* v_head_1173_; lean_object* v_tail_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1192_; 
v_head_1173_ = lean_ctor_get(v_x_1166_, 0);
v_tail_1174_ = lean_ctor_get(v_x_1166_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_x_1166_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1176_ = v_x_1166_;
v_isShared_1177_ = v_isSharedCheck_1192_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_tail_1174_);
lean_inc(v_head_1173_);
lean_dec(v_x_1166_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1192_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; 
lean_inc(v___x_1165_);
lean_inc_ref(v_postNode_1164_);
lean_inc_ref(v_preNode_1163_);
v___x_1178_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1163_, v_postNode_1164_, v___x_1165_, v_head_1173_, v___y_1168_, v___y_1169_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_x_1167_);
lean_ctor_set(v___x_1176_, 0, v_a_1179_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1179_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_x_1167_);
v___x_1181_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
v_x_1166_ = v_tail_1174_;
v_x_1167_ = v___x_1181_;
goto _start;
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
lean_del_object(v___x_1176_);
lean_dec(v_tail_1174_);
lean_dec(v_x_1167_);
lean_dec(v___x_1165_);
lean_dec_ref(v_postNode_1164_);
lean_dec_ref(v_preNode_1163_);
v_a_1184_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1178_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1178_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_preNode_1193_, lean_object* v_postNode_1194_, lean_object* v___x_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1193_, v_postNode_1194_, v___x_1195_, v_x_1196_, v_x_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg___boxed(lean_object* v_preNode_1202_, lean_object* v_postNode_1203_, lean_object* v_x_1204_, lean_object* v_x_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1202_, v_postNode_1203_, v_x_1204_, v_x_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* v_preNode_1210_, lean_object* v_postNode_1211_, lean_object* v_ctx_x3f_1212_, lean_object* v_t_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___f_1217_; lean_object* v___x_1218_; 
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1217_, 0, v_postNode_1211_);
v___x_1218_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1210_, v___f_1217_, v_ctx_x3f_1212_, v_t_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1226_; 
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1218_, 0);
lean_dec(v_unused_1227_);
v___x_1220_ = v___x_1218_;
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1218_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1226_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_box(0);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_a_1228_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1218_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1218_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* v_preNode_1236_, lean_object* v_postNode_1237_, lean_object* v_ctx_x3f_1238_, lean_object* v_t_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v_preNode_1236_, v_postNode_1237_, v_ctx_x3f_1238_, v_t_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(uint8_t v___x_1244_, lean_object* v_val_1245_, lean_object* v_val_1246_, lean_object* v_as_1247_, size_t v_sz_1248_, size_t v_i_1249_, lean_object* v_b_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_lt(v_i_1249_, v_sz_1248_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_val_1246_);
lean_dec(v_val_1245_);
v___x_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_b_1250_);
return v___x_1255_;
}
else
{
lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v_a_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1256_ = lean_box(v___x_1244_);
v___f_1257_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1257_, 0, v___x_1256_);
v___x_1258_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1259_ = lean_box(0);
lean_inc_ref(v_val_1246_);
lean_inc(v_val_1245_);
v___f_1260_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___lam__2___boxed), 10, 4);
lean_closure_set(v___f_1260_, 0, v_val_1245_);
lean_closure_set(v___f_1260_, 1, v___x_1259_);
lean_closure_set(v___f_1260_, 2, v_val_1246_);
lean_closure_set(v___f_1260_, 3, v___x_1258_);
v_a_1261_ = lean_array_uget_borrowed(v_as_1247_, v_i_1249_);
v___x_1262_ = lean_box(0);
lean_inc(v_a_1261_);
v___x_1263_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6(v___f_1257_, v___f_1260_, v___x_1262_, v_a_1261_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1263_) == 0)
{
size_t v___x_1264_; size_t v___x_1265_; 
lean_dec_ref_known(v___x_1263_, 1);
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1249_, v___x_1264_);
v_i_1249_ = v___x_1265_;
v_b_1250_ = v___x_1259_;
goto _start;
}
else
{
lean_dec_ref(v_val_1246_);
lean_dec(v_val_1245_);
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* v___x_1267_, lean_object* v_val_1268_, lean_object* v_val_1269_, lean_object* v_as_1270_, lean_object* v_sz_1271_, lean_object* v_i_1272_, lean_object* v_b_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
uint8_t v___x_23432__boxed_1277_; size_t v_sz_boxed_1278_; size_t v_i_boxed_1279_; lean_object* v_res_1280_; 
v___x_23432__boxed_1277_ = lean_unbox(v___x_1267_);
v_sz_boxed_1278_ = lean_unbox_usize(v_sz_1271_);
lean_dec(v_sz_1271_);
v_i_boxed_1279_ = lean_unbox_usize(v_i_1272_);
lean_dec(v_i_1272_);
v_res_1280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_23432__boxed_1277_, v_val_1268_, v_val_1269_, v_as_1270_, v_sz_boxed_1278_, v_i_boxed_1279_, v_b_1273_, v___y_1274_, v___y_1275_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v_as_1270_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 0)
{
return v_x_1281_;
}
else
{
lean_object* v_key_1283_; lean_object* v_value_1284_; lean_object* v_tail_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_key_1283_ = lean_ctor_get(v_x_1282_, 0);
v_value_1284_ = lean_ctor_get(v_x_1282_, 1);
v_tail_1285_ = lean_ctor_get(v_x_1282_, 2);
lean_inc(v_value_1284_);
lean_inc(v_key_1283_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_key_1283_);
lean_ctor_set(v___x_1286_, 1, v_value_1284_);
v___x_1287_ = lean_array_push(v_x_1281_, v___x_1286_);
v_x_1281_ = v___x_1287_;
v_x_1282_ = v_tail_1285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_x_1289_, v_x_1290_);
lean_dec(v_x_1290_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(lean_object* v_as_1292_, size_t v_i_1293_, size_t v_stop_1294_, lean_object* v_b_1295_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_eq(v_i_1293_, v_stop_1294_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; 
v___x_1297_ = lean_array_uget_borrowed(v_as_1292_, v_i_1293_);
v___x_1298_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__11(v_b_1295_, v___x_1297_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1293_, v___x_1299_);
v_i_1293_ = v___x_1300_;
v_b_1295_ = v___x_1298_;
goto _start;
}
else
{
return v_b_1295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12___boxed(lean_object* v_as_1302_, lean_object* v_i_1303_, lean_object* v_stop_1304_, lean_object* v_b_1305_){
_start:
{
size_t v_i_boxed_1306_; size_t v_stop_boxed_1307_; lean_object* v_res_1308_; 
v_i_boxed_1306_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_stop_boxed_1307_ = lean_unbox_usize(v_stop_1304_);
lean_dec(v_stop_1304_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_as_1302_, v_i_boxed_1306_, v_stop_boxed_1307_, v_b_1305_);
lean_dec_ref(v_as_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_scopes_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_opts_1316_; lean_object* v___x_1317_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_scopes_1313_ = lean_ctor_get(v___x_1312_, 2);
lean_inc(v_scopes_1313_);
lean_dec(v___x_1312_);
v___x_1314_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1315_ = l_List_head_x21___redArg(v___x_1314_, v_scopes_1313_);
lean_dec(v_scopes_1313_);
v_opts_1316_ = lean_ctor_get(v___x_1315_, 1);
lean_inc_ref(v_opts_1316_);
lean_dec(v___x_1315_);
v___x_1317_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(v_opts_1316_, v___y_1310_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1321_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_unsigned_to_nat(16u);
v___x_1324_ = lean_mk_array(v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v___x_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* v_cmdStx_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1403_; 
v___x_1332_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_constructorNameAsVariable_spec__0(v___y_1329_, v___y_1330_);
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1403_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1403_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1337_ = l_Lean_Linter_linter_constructorNameAsVariable;
v___x_1338_ = l_Lean_Linter_getLinterValue(v___x_1337_, v_a_1333_);
lean_dec(v_a_1333_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_box(0);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1339_);
v___x_1341_ = v___x_1335_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
else
{
uint8_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = 0;
v___x_1344_ = l_Lean_Syntax_getRange_x3f(v_cmdStx_1328_, v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_infoState_1350_; lean_object* v_trees_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
lean_del_object(v___x_1335_);
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = lean_st_ref_get(v___y_1330_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_obj_once(&l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1, &l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1_once, _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
v___x_1349_ = lean_st_mk_ref(v___x_1348_);
v_infoState_1350_ = lean_ctor_get(v___x_1346_, 8);
lean_inc_ref(v_infoState_1350_);
lean_dec(v___x_1346_);
v_trees_1351_ = lean_ctor_get(v_infoState_1350_, 2);
lean_inc_ref(v_trees_1351_);
lean_dec_ref(v_infoState_1350_);
v___x_1352_ = l_Lean_PersistentArray_toArray___redArg(v_trees_1351_);
lean_dec_ref(v_trees_1351_);
v___x_1353_ = lean_box(0);
v_sz_1354_ = lean_array_size(v___x_1352_);
v___x_1355_ = ((size_t)0ULL);
lean_inc(v___x_1349_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(v___x_1338_, v___x_1349_, v_val_1345_, v___x_1352_, v_sz_1354_, v___x_1355_, v___x_1353_, v___y_1329_, v___y_1330_);
lean_dec_ref(v___x_1352_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; lean_object* v___y_1359_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1383_; lean_object* v_size_1389_; lean_object* v_buckets_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
lean_dec_ref_known(v___x_1356_, 1);
v___x_1357_ = lean_st_ref_get(v___x_1349_);
lean_dec(v___x_1349_);
v_size_1389_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_size_1389_);
v_buckets_1390_ = lean_ctor_get(v___x_1357_, 1);
lean_inc_ref(v_buckets_1390_);
lean_dec(v___x_1357_);
v___x_1391_ = lean_mk_empty_array_with_capacity(v_size_1389_);
lean_dec(v_size_1389_);
v___x_1392_ = lean_array_get_size(v_buckets_1390_);
v___x_1393_ = lean_nat_dec_lt(v___x_1347_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_dec_ref(v_buckets_1390_);
v___y_1383_ = v___x_1391_;
goto v___jp_1382_;
}
else
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_nat_dec_le(v___x_1392_, v___x_1392_);
if (v___x_1394_ == 0)
{
if (v___x_1393_ == 0)
{
lean_dec_ref(v_buckets_1390_);
v___y_1383_ = v___x_1391_;
goto v___jp_1382_;
}
else
{
size_t v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_usize_of_nat(v___x_1392_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1390_, v___x_1355_, v___x_1395_, v___x_1391_);
lean_dec_ref(v_buckets_1390_);
v___y_1383_ = v___x_1396_;
goto v___jp_1382_;
}
}
else
{
size_t v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_usize_of_nat(v___x_1392_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__12(v_buckets_1390_, v___x_1355_, v___x_1397_, v___x_1391_);
lean_dec_ref(v_buckets_1390_);
v___y_1383_ = v___x_1398_;
goto v___jp_1382_;
}
}
v___jp_1358_:
{
size_t v_sz_1360_; lean_object* v___x_1361_; 
v_sz_1360_ = lean_array_size(v___y_1359_);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__9(v___y_1359_, v_sz_1360_, v___x_1355_, v___x_1353_, v___y_1329_, v___y_1330_);
lean_dec_ref(v___y_1359_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v___x_1361_, 0);
lean_dec(v_unused_1369_);
v___x_1363_ = v___x_1361_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_dec(v___x_1361_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1353_);
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1353_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
return v___x_1361_;
}
}
v___jp_1370_:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v___y_1371_, v___y_1373_, v___y_1372_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec(v___y_1371_);
v___y_1359_ = v___x_1375_;
goto v___jp_1358_;
}
v___jp_1376_:
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_le(v___y_1380_, v___y_1378_);
if (v___x_1381_ == 0)
{
lean_dec(v___y_1378_);
lean_inc(v___y_1380_);
v___y_1371_ = v___y_1377_;
v___y_1372_ = v___y_1380_;
v___y_1373_ = v___y_1379_;
v___y_1374_ = v___y_1380_;
goto v___jp_1370_;
}
else
{
v___y_1371_ = v___y_1377_;
v___y_1372_ = v___y_1380_;
v___y_1373_ = v___y_1379_;
v___y_1374_ = v___y_1378_;
goto v___jp_1370_;
}
}
v___jp_1382_:
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = lean_array_get_size(v___y_1383_);
v___x_1385_ = lean_nat_dec_eq(v___x_1384_, v___x_1347_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1386_ = lean_unsigned_to_nat(1u);
v___x_1387_ = lean_nat_sub(v___x_1384_, v___x_1386_);
v___x_1388_ = lean_nat_dec_le(v___x_1347_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_inc(v___x_1387_);
v___y_1377_ = v___x_1384_;
v___y_1378_ = v___x_1387_;
v___y_1379_ = v___y_1383_;
v___y_1380_ = v___x_1387_;
goto v___jp_1376_;
}
else
{
v___y_1377_ = v___x_1384_;
v___y_1378_ = v___x_1387_;
v___y_1379_ = v___y_1383_;
v___y_1380_ = v___x_1347_;
goto v___jp_1376_;
}
}
else
{
v___y_1359_ = v___y_1383_;
goto v___jp_1358_;
}
}
}
else
{
lean_dec(v___x_1349_);
return v___x_1356_;
}
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec(v___x_1344_);
v___x_1399_ = lean_box(0);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1399_);
v___x_1401_ = v___x_1335_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* v_cmdStx_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Linter_constructorNameAsVariable___lam__0(v_cmdStx_1404_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v_cmdStx_1404_);
return v_res_1408_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* v_00_u03b2_1418_, lean_object* v_m_1419_, lean_object* v_a_1420_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___redArg(v_m_1419_, v_a_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* v_00_u03b2_1422_, lean_object* v_m_1423_, lean_object* v_a_1424_){
_start:
{
uint8_t v_res_1425_; lean_object* v_r_1426_; 
v_res_1425_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1(v_00_u03b2_1422_, v_m_1423_, v_a_1424_);
lean_dec_ref(v_a_1424_);
lean_dec_ref(v_m_1423_);
v_r_1426_ = lean_box(v_res_1425_);
return v_r_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_a_1429_, lean_object* v_b_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(v_m_1428_, v_a_1429_, v_b_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* v_str_1432_, lean_object* v_val_1433_, lean_object* v_info_1434_, lean_object* v___x_1435_, lean_object* v_val_1436_, uint8_t v___x_1437_, lean_object* v_as_1438_, lean_object* v_as_x27_1439_, lean_object* v_b_1440_, lean_object* v_a_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___redArg(v_str_1432_, v_val_1433_, v_info_1434_, v___x_1435_, v_val_1436_, v___x_1437_, v_as_x27_1439_, v_b_1440_, v___y_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* v_str_1446_, lean_object* v_val_1447_, lean_object* v_info_1448_, lean_object* v___x_1449_, lean_object* v_val_1450_, lean_object* v___x_1451_, lean_object* v_as_1452_, lean_object* v_as_x27_1453_, lean_object* v_b_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v___x_23724__boxed_1459_; lean_object* v_res_1460_; 
v___x_23724__boxed_1459_ = lean_unbox(v___x_1451_);
v_res_1460_ = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__5(v_str_1446_, v_val_1447_, v_info_1448_, v___x_1449_, v_val_1450_, v___x_23724__boxed_1459_, v_as_1452_, v_as_x27_1453_, v_b_1454_, v_a_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v_as_x27_1453_);
lean_dec(v_as_1452_);
lean_dec_ref(v_info_1448_);
lean_dec(v_val_1447_);
lean_dec_ref(v_str_1446_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* v_n_1461_, lean_object* v_as_1462_, lean_object* v_lo_1463_, lean_object* v_hi_1464_, lean_object* v_w_1465_, lean_object* v_hlo_1466_, lean_object* v_hhi_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___redArg(v_n_1461_, v_as_1462_, v_lo_1463_, v_hi_1464_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* v_n_1469_, lean_object* v_as_1470_, lean_object* v_lo_1471_, lean_object* v_hi_1472_, lean_object* v_w_1473_, lean_object* v_hlo_1474_, lean_object* v_hhi_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10(v_n_1469_, v_as_1470_, v_lo_1471_, v_hi_1472_, v_w_1473_, v_hlo_1474_, v_hhi_1475_);
lean_dec(v_hi_1472_);
lean_dec(v_n_1469_);
return v_res_1476_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(lean_object* v_00_u03b2_1477_, lean_object* v_a_1478_, lean_object* v_x_1479_){
_start:
{
uint8_t v___x_1480_; 
v___x_1480_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___redArg(v_a_1478_, v_x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1481_, lean_object* v_a_1482_, lean_object* v_x_1483_){
_start:
{
uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_res_1484_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__1_spec__1(v_00_u03b2_1481_, v_a_1482_, v_x_1483_);
lean_dec(v_x_1483_);
lean_dec_ref(v_a_1482_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4(lean_object* v_00_u03b2_1486_, lean_object* v_data_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4___redArg(v_data_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5(lean_object* v_00_u03b2_1489_, lean_object* v_a_1490_, lean_object* v_b_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__5___redArg(v_a_1490_, v_b_1491_, v_x_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(lean_object* v_00_u03b1_1494_, lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___redArg(v_msg_1495_, v___y_1496_, v___y_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__11(v_00_u03b1_1500_, v_msg_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(lean_object* v_00_u03b1_1506_, lean_object* v_preNode_1507_, lean_object* v_postNode_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___redArg(v_preNode_1507_, v_postNode_1508_, v_x_1509_, v_x_1510_, v___y_1511_, v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1515_, lean_object* v_preNode_1516_, lean_object* v_postNode_1517_, lean_object* v_x_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9(v_00_u03b1_1515_, v_preNode_1516_, v_postNode_1517_, v_x_1518_, v_x_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(lean_object* v_n_1524_, lean_object* v_lo_1525_, lean_object* v_hi_1526_, lean_object* v_hhi_1527_, lean_object* v_pivot_1528_, lean_object* v_as_1529_, lean_object* v_i_1530_, lean_object* v_k_1531_, lean_object* v_ilo_1532_, lean_object* v_ik_1533_, lean_object* v_w_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___redArg(v_hi_1526_, v_pivot_1528_, v_as_1529_, v_i_1530_, v_k_1531_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15___boxed(lean_object* v_n_1536_, lean_object* v_lo_1537_, lean_object* v_hi_1538_, lean_object* v_hhi_1539_, lean_object* v_pivot_1540_, lean_object* v_as_1541_, lean_object* v_i_1542_, lean_object* v_k_1543_, lean_object* v_ilo_1544_, lean_object* v_ik_1545_, lean_object* v_w_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__10_spec__15(v_n_1536_, v_lo_1537_, v_hi_1538_, v_hhi_1539_, v_pivot_1540_, v_as_1541_, v_i_1542_, v_k_1543_, v_ilo_1544_, v_ik_1545_, v_w_1546_);
lean_dec_ref(v_pivot_1540_);
lean_dec(v_hi_1538_);
lean_dec(v_lo_1537_);
lean_dec(v_n_1536_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_1548_, lean_object* v_i_1549_, lean_object* v_source_1550_, lean_object* v_target_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6___redArg(v_i_1549_, v_source_1550_, v_target_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1553_, lean_object* v_preNode_1554_, lean_object* v_postNode_1555_, lean_object* v___x_1556_, lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___redArg(v_preNode_1554_, v_postNode_1555_, v___x_1556_, v_x_1557_, v_x_1558_, v___y_1559_, v___y_1560_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1563_, lean_object* v_preNode_1564_, lean_object* v_postNode_1565_, lean_object* v___x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__9_spec__12(v_00_u03b1_1563_, v_preNode_1564_, v_postNode_1565_, v___x_1566_, v_x_1567_, v_x_1568_, v___y_1569_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec_ref(v___y_1569_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(lean_object* v_msgData_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___redArg(v_msgData_1573_, v___y_1575_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22___boxed(lean_object* v_msgData_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__7_spec__11_spec__15_spec__22(v_msgData_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__3_spec__4_spec__6_spec__15___redArg(v_x_1584_, v_x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
v___x_1589_ = l_Lean_Elab_Command_addLinter(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return v_res_1591_;
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
