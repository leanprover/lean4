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
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "constructorNameAsVariable"};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(145, 93, 54, 211, 83, 91, 108, 28)}};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "enable the linter that warns when bound variable names are nullary constructor names"};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
static const lean_string_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 65, 101, 89, 237, 205, 227, 46)}};
static const lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_constructorNameAsVariable;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__6;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___closed__0_value;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__2_value;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Local variable '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__0_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' resembles constructor '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__2_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "' - "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__4_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "write '."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__6_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "' (with a dot) or '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__8_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "' to use the constructor."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__10_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5_spec__14___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3___redArg(lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_TermInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn_x27(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__0;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__1_value;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__2_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__3;
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0;
static lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1;
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_constructorNameAsVariable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_constructorNameAsVariable___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_constructorNameAsVariable___closed__0 = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__0_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 75, 81, 128, 80, 183, 232, 251)}};
static const lean_object* l_Lean_Linter_constructorNameAsVariable___closed__1 = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value;
static const lean_ctor_object l_Lean_Linter_constructorNameAsVariable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__0_value),((lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__1_value)}};
static const lean_object* l_Lean_Linter_constructorNameAsVariable___closed__2 = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_constructorNameAsVariable = (const lean_object*)&l_Lean_Linter_constructorNameAsVariable___closed__2_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5_spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 0, 1);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, 0, x_21);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_19);
lean_inc(x_1);
x_23 = lean_register_option(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_24 = x_23;
} else {
 lean_dec_ref(x_23);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_18);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
x_3 = l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__10(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_constructorNameAsVariable_spec__10(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_nat_dec_lt(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___closed__0));
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__2;
x_12 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__6;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_82; uint8_t x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; uint8_t x_145; uint8_t x_158; 
x_139 = 2;
x_158 = l_Lean_instBEqMessageSeverity_beq(x_3, x_139);
if (x_158 == 0)
{
x_145 = x_158;
goto block_157;
}
else
{
uint8_t x_159; 
lean_inc_ref(x_2);
x_159 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_145 = x_159;
goto block_157;
}
block_81:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_st_ref_take(x_15);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_21, 3);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_8);
lean_ctor_set(x_29, 3, x_14);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_4);
x_30 = l_Lean_MessageLog_add(x_29, x_26);
lean_ctor_set(x_22, 1, x_30);
x_31 = lean_st_ref_set(x_15, x_22);
x_32 = lean_box(0);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
x_37 = lean_ctor_get(x_22, 4);
x_38 = lean_ctor_get(x_22, 5);
x_39 = lean_ctor_get(x_22, 6);
x_40 = lean_ctor_get(x_22, 7);
x_41 = lean_ctor_get(x_22, 8);
x_42 = lean_ctor_get(x_22, 9);
x_43 = lean_ctor_get(x_22, 10);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_23);
lean_ctor_set(x_44, 1, x_24);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_12);
x_46 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_11);
lean_ctor_set(x_46, 2, x_8);
lean_ctor_set(x_46, 3, x_14);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 2, x_4);
x_47 = l_Lean_MessageLog_add(x_46, x_34);
x_48 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
lean_ctor_set(x_48, 4, x_37);
lean_ctor_set(x_48, 5, x_38);
lean_ctor_set(x_48, 6, x_39);
lean_ctor_set(x_48, 7, x_40);
lean_ctor_set(x_48, 8, x_41);
lean_ctor_set(x_48, 9, x_42);
lean_ctor_set(x_48, 10, x_43);
x_49 = lean_st_ref_set(x_15, x_48);
x_50 = lean_box(0);
lean_ctor_set(x_19, 0, x_50);
return x_19;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_st_ref_take(x_15);
x_53 = lean_ctor_get(x_18, 2);
lean_inc(x_53);
lean_dec(x_18);
x_54 = lean_ctor_get(x_51, 3);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_52, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 5);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 6);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_52, 7);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_52, 8);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_52, 9);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_52, 10);
lean_inc_ref(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 lean_ctor_release(x_52, 7);
 lean_ctor_release(x_52, 8);
 lean_ctor_release(x_52, 9);
 lean_ctor_release(x_52, 10);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_54);
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_12);
x_69 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_69, 0, x_9);
lean_ctor_set(x_69, 1, x_11);
lean_ctor_set(x_69, 2, x_8);
lean_ctor_set(x_69, 3, x_14);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_69, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_69, sizeof(void*)*5 + 2, x_4);
x_70 = l_Lean_MessageLog_add(x_69, x_56);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 11, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_57);
lean_ctor_set(x_71, 3, x_58);
lean_ctor_set(x_71, 4, x_59);
lean_ctor_set(x_71, 5, x_60);
lean_ctor_set(x_71, 6, x_61);
lean_ctor_set(x_71, 7, x_62);
lean_ctor_set(x_71, 8, x_63);
lean_ctor_set(x_71, 9, x_64);
lean_ctor_set(x_71, 10, x_65);
x_72 = lean_st_ref_set(x_15, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_18);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
x_75 = !lean_is_exclusive(x_19);
if (x_75 == 0)
{
return x_19;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_19, 0);
lean_inc(x_76);
lean_dec(x_19);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_9);
lean_dec(x_8);
x_78 = !lean_is_exclusive(x_17);
if (x_78 == 0)
{
return x_17;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_17, 0);
lean_inc(x_79);
lean_dec(x_17);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
block_115:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_89);
x_90 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
lean_dec_ref(x_5);
x_91 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_92 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg(x_91, x_6);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_89);
x_95 = l_Lean_FileMap_toPosition(x_89, x_84);
lean_dec(x_84);
x_96 = l_Lean_FileMap_toPosition(x_89, x_87);
lean_dec(x_87);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___closed__0));
if (x_90 == 0)
{
lean_free_object(x_92);
x_8 = x_97;
x_9 = x_88;
x_10 = x_83;
x_11 = x_95;
x_12 = x_94;
x_13 = x_85;
x_14 = x_98;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_box(x_82);
x_100 = lean_box(x_90);
x_101 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___boxed), 3, 2);
lean_closure_set(x_101, 0, x_99);
lean_closure_set(x_101, 1, x_100);
lean_inc(x_94);
x_102 = l_Lean_MessageData_hasTag(x_101, x_94);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec_ref(x_97);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_88);
x_103 = lean_box(0);
lean_ctor_set(x_92, 0, x_103);
return x_92;
}
else
{
lean_free_object(x_92);
x_8 = x_97;
x_9 = x_88;
x_10 = x_83;
x_11 = x_95;
x_12 = x_94;
x_13 = x_85;
x_14 = x_98;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
lean_dec(x_92);
lean_inc_ref(x_89);
x_105 = l_Lean_FileMap_toPosition(x_89, x_84);
lean_dec(x_84);
x_106 = l_Lean_FileMap_toPosition(x_89, x_87);
lean_dec(x_87);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___closed__0));
if (x_90 == 0)
{
x_8 = x_107;
x_9 = x_88;
x_10 = x_83;
x_11 = x_105;
x_12 = x_104;
x_13 = x_85;
x_14 = x_108;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_box(x_82);
x_110 = lean_box(x_90);
x_111 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___lam__0___boxed), 3, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
lean_inc(x_104);
x_112 = l_Lean_MessageData_hasTag(x_111, x_104);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_88);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
x_8 = x_107;
x_9 = x_88;
x_10 = x_83;
x_11 = x_105;
x_12 = x_104;
x_13 = x_85;
x_14 = x_108;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
}
}
}
block_124:
{
lean_object* x_122; 
x_122 = l_Lean_Syntax_getTailPos_x3f(x_117, x_118);
lean_dec(x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_inc(x_121);
x_82 = x_116;
x_83 = x_118;
x_84 = x_121;
x_85 = x_119;
x_86 = lean_box(0);
x_87 = x_121;
goto block_115;
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_82 = x_116;
x_83 = x_118;
x_84 = x_121;
x_85 = x_119;
x_86 = lean_box(0);
x_87 = x_123;
goto block_115;
}
}
block_138:
{
lean_object* x_129; 
x_129 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_replaceRef(x_1, x_130);
lean_dec(x_130);
x_132 = l_Lean_Syntax_getPos_x3f(x_131, x_127);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_unsigned_to_nat(0u);
x_116 = x_125;
x_117 = x_131;
x_118 = x_127;
x_119 = x_128;
x_120 = lean_box(0);
x_121 = x_133;
goto block_124;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec_ref(x_132);
x_116 = x_125;
x_117 = x_131;
x_118 = x_127;
x_119 = x_128;
x_120 = lean_box(0);
x_121 = x_134;
goto block_124;
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_135 = !lean_is_exclusive(x_129);
if (x_135 == 0)
{
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
block_144:
{
if (x_143 == 0)
{
x_125 = x_140;
x_126 = lean_box(0);
x_127 = x_142;
x_128 = x_3;
goto block_138;
}
else
{
x_125 = x_140;
x_126 = lean_box(0);
x_127 = x_142;
x_128 = x_139;
goto block_138;
}
}
block_157:
{
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_146 = lean_st_ref_get(x_6);
x_147 = lean_ctor_get(x_146, 2);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_Elab_Command_instInhabitedScope_default;
x_149 = l_List_head_x21___redArg(x_148, x_147);
lean_dec(x_147);
x_150 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_150);
lean_dec(x_149);
x_151 = 1;
x_152 = l_Lean_instBEqMessageSeverity_beq(x_3, x_151);
if (x_152 == 0)
{
lean_dec_ref(x_150);
x_140 = x_145;
x_141 = lean_box(0);
x_142 = x_145;
x_143 = x_152;
goto block_144;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_warningAsError;
x_154 = l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1(x_150, x_153);
lean_dec_ref(x_150);
x_140 = x_145;
x_141 = lean_box(0);
x_142 = x_145;
x_143 = x_154;
goto block_144;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14(x_1, x_2, x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1;
lean_inc(x_8);
x_11 = l_Lean_MessageData_ofName(x_8);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
x_12 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_MessageData_note(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10(x_2, x_16, x_4, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1;
lean_inc(x_18);
x_20 = l_Lean_MessageData_ofName(x_18);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10(x_2, x_26, x_4, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = l_Lean_Linter_linter_constructorNameAsVariable;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1;
x_22 = l_Lean_MessageData_ofName(x_18);
lean_inc_ref(x_22);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_22);
lean_ctor_set(x_15, 0, x_21);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_15);
x_24 = l_Lean_MessageData_ofName(x_19);
lean_inc_ref(x_24);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_24);
lean_ctor_set(x_10, 0, x_12);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_25);
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_inc_ref(x_5);
x_35 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(x_20, x_17, x_34, x_5, x_6);
lean_dec(x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec_ref(x_35);
x_36 = lean_box(0);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_4 = x_36;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_35;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = l_Lean_Linter_linter_constructorNameAsVariable;
x_44 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1;
x_45 = l_Lean_MessageData_ofName(x_41);
lean_inc_ref(x_45);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_47);
lean_ctor_set(x_12, 0, x_46);
x_48 = l_Lean_MessageData_ofName(x_42);
lean_inc_ref(x_48);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_48);
lean_ctor_set(x_10, 0, x_12);
x_49 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
x_56 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
lean_inc_ref(x_5);
x_59 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(x_43, x_40, x_58, x_5, x_6);
lean_dec(x_40);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; size_t x_61; size_t x_62; 
lean_dec_ref(x_59);
x_60 = lean_box(0);
x_61 = 1;
x_62 = lean_usize_add(x_3, x_61);
x_3 = x_62;
x_4 = x_60;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_59;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_64 = lean_ctor_get(x_12, 1);
x_65 = lean_ctor_get(x_12, 0);
lean_inc(x_64);
lean_inc(x_65);
lean_dec(x_12);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = l_Lean_Linter_linter_constructorNameAsVariable;
x_70 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1;
x_71 = l_Lean_MessageData_ofName(x_66);
lean_inc_ref(x_71);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(7, 2, 0);
} else {
 x_72 = x_68;
 lean_ctor_set_tag(x_72, 7);
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MessageData_ofName(x_67);
lean_inc_ref(x_75);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_75);
lean_ctor_set(x_10, 0, x_74);
x_76 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_10);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_71);
x_80 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
x_83 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
lean_inc_ref(x_5);
x_86 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(x_69, x_65, x_85, x_5, x_6);
lean_dec(x_65);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; size_t x_88; size_t x_89; 
lean_dec_ref(x_86);
x_87 = lean_box(0);
x_88 = 1;
x_89 = lean_usize_add(x_3, x_88);
x_3 = x_89;
x_4 = x_87;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_86;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_dec(x_10);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
x_98 = l_Lean_Linter_linter_constructorNameAsVariable;
x_99 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1;
x_100 = l_Lean_MessageData_ofName(x_95);
lean_inc_ref(x_100);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(7, 2, 0);
} else {
 x_101 = x_97;
 lean_ctor_set_tag(x_101, 7);
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3;
if (lean_is_scalar(x_94)) {
 x_103 = lean_alloc_ctor(7, 2, 0);
} else {
 x_103 = x_94;
 lean_ctor_set_tag(x_103, 7);
}
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MessageData_ofName(x_96);
lean_inc_ref(x_104);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_100);
x_110 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
x_113 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
lean_inc_ref(x_5);
x_116 = l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6(x_98, x_93, x_115, x_5, x_6);
lean_dec(x_93);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; size_t x_118; size_t x_119; 
lean_dec_ref(x_116);
x_117 = lean_box(0);
x_118 = 1;
x_119 = lean_usize_add(x_3, x_118);
x_3 = x_119;
x_4 = x_117;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5_spec__14___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Syntax_instHashableRange_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Syntax_instHashableRange_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5_spec__14___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Syntax_instBEqRange_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_Syntax_instBEqRange_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_Syntax_instBEqRange_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_31; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_14 = x_7;
} else {
 lean_dec_ref(x_7);
 x_14 = lean_box(0);
}
x_15 = lean_st_ref_get(x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
lean_inc(x_12);
x_31 = l_Lean_Environment_find_x3f(x_16, x_12, x_6);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
if (lean_obj_tag(x_32) == 6)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 4);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
x_18 = lean_box(0);
goto block_30;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
x_7 = x_13;
x_8 = x_17;
goto _start;
}
}
else
{
lean_dec(x_32);
x_18 = lean_box(0);
goto block_30;
}
}
else
{
lean_dec(x_31);
x_18 = lean_box(0);
goto block_30;
}
block_30:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_string_dec_eq(x_19, x_1);
if (x_20 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_12);
x_7 = x_13;
x_8 = x_17;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_st_ref_take(x_2);
x_23 = l_Lean_Elab_Info_stx(x_3);
lean_inc(x_4);
if (lean_is_scalar(x_14)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_14;
 lean_ctor_set_tag(x_24, 0);
}
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc_ref(x_5);
x_26 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(x_22, x_5, x_25);
x_27 = lean_st_ref_set(x_2, x_26);
x_7 = x_13;
x_8 = x_17;
goto _start;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
x_7 = x_13;
x_8 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
x_12 = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Linter_constructorNameAsVariable_spec__3___redArg(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_whnf(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_10, 3);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 2);
x_14 = lean_ctor_get_uint8(x_10, sizeof(void*)*4);
x_15 = lean_ctor_get(x_11, 0);
x_16 = l_Lean_Elab_Info_range_x3f(x_5);
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_st_ref_get(x_1);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg(x_19, x_18);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Info_stx(x_5);
x_22 = l_Lean_Syntax_getHeadInfo(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
if (x_14 == 0)
{
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
lean_object* x_23; 
lean_inc(x_15);
lean_inc_ref(x_12);
x_23 = lean_local_ctx_find(x_12, x_15);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_18, 0);
x_27 = l_Lean_Syntax_Range_contains(x_3, x_26, x_20);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_21);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_25)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_25;
 lean_ctor_set_tag(x_28, 0);
}
lean_ctor_set(x_28, 0, x_2);
return x_28;
}
else
{
if (x_20 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_LocalDecl_userName(x_24);
lean_dec(x_24);
x_30 = l_Lean_Name_hasMacroScopes(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_31, 4);
x_33 = l_Lean_Linter_linter_constructorNameAsVariable;
x_34 = l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_21);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_25)) {
 x_35 = lean_alloc_ctor(0, 1, 0);
} else {
 x_35 = x_25;
 lean_ctor_set_tag(x_35, 0);
}
lean_ctor_set(x_35, 0, x_2);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_38);
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_98; 
lean_free_object(x_16);
x_98 = lean_ctor_get(x_13, 0);
lean_inc(x_98);
x_39 = x_98;
x_40 = x_7;
x_41 = x_8;
x_42 = lean_box(0);
goto block_97;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_inc_ref(x_11);
x_99 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_99, 0, x_11);
lean_inc_ref(x_4);
lean_inc_ref(x_10);
x_100 = l_Lean_Elab_TermInfo_runMetaM___redArg(x_10, x_4, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
lean_free_object(x_16);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_39 = x_101;
x_40 = x_7;
x_41 = x_8;
x_42 = lean_box(0);
goto block_97;
}
else
{
uint8_t x_102; 
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_102 = !lean_is_exclusive(x_18);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_18, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_18, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_100);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_100, 0);
x_107 = lean_ctor_get(x_7, 7);
x_108 = lean_io_error_to_string(x_106);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_108);
x_109 = l_Lean_MessageData_ofFormat(x_16);
lean_inc(x_107);
lean_ctor_set(x_18, 1, x_109);
lean_ctor_set(x_18, 0, x_107);
lean_ctor_set(x_100, 0, x_18);
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
lean_dec(x_100);
x_111 = lean_ctor_get(x_7, 7);
x_112 = lean_io_error_to_string(x_110);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_112);
x_113 = l_Lean_MessageData_ofFormat(x_16);
lean_inc(x_111);
lean_ctor_set(x_18, 1, x_113);
lean_ctor_set(x_18, 0, x_111);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_18);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_18);
x_115 = lean_ctor_get(x_100, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_116 = x_100;
} else {
 lean_dec_ref(x_100);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_7, 7);
x_118 = lean_io_error_to_string(x_115);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 0, x_118);
x_119 = l_Lean_MessageData_ofFormat(x_16);
lean_inc(x_117);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_116)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_116;
}
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
}
}
else
{
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_25);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
block_97:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1___boxed), 6, 1);
lean_closure_set(x_43, 0, x_39);
lean_inc_ref(x_10);
x_44 = l_Lean_Elab_TermInfo_runMetaM___redArg(x_10, x_4, x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_25);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l_Lean_Expr_getAppFn_x27(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 4)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_st_ref_get(x_41);
x_50 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_50);
lean_dec(x_49);
x_51 = l_Lean_Environment_find_x3f(x_50, x_48, x_30);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
if (lean_obj_tag(x_52) == 5)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_44);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 4);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(x_38, x_1, x_5, x_36, x_18, x_30, x_54, x_2, x_41);
lean_dec_ref(x_5);
lean_dec_ref(x_38);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_2);
return x_55;
}
else
{
lean_object* x_58; 
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_2);
return x_58;
}
}
else
{
return x_55;
}
}
else
{
lean_dec(x_52);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_ctor_set(x_44, 0, x_2);
return x_44;
}
}
else
{
lean_dec(x_51);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_ctor_set(x_44, 0, x_2);
return x_44;
}
}
else
{
lean_dec_ref(x_47);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_ctor_set(x_44, 0, x_2);
return x_44;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
lean_dec(x_44);
x_60 = l_Lean_Expr_getAppFn_x27(x_59);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 4)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_st_ref_get(x_41);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
lean_dec(x_62);
x_64 = l_Lean_Environment_find_x3f(x_63, x_61, x_30);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
if (lean_obj_tag(x_65) == 5)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 4);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(x_38, x_1, x_5, x_36, x_18, x_30, x_67, x_2, x_41);
lean_dec_ref(x_5);
lean_dec_ref(x_38);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_69 = x_68;
} else {
 lean_dec_ref(x_68);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
return x_68;
}
}
else
{
lean_object* x_71; 
lean_dec(x_65);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_18);
lean_dec_ref(x_5);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_2);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_64);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_18);
lean_dec_ref(x_5);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_2);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec_ref(x_60);
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec(x_18);
lean_dec_ref(x_5);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_2);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec_ref(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_5);
x_74 = !lean_is_exclusive(x_18);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_18, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_18, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_44);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_44, 0);
x_79 = lean_ctor_get(x_40, 7);
x_80 = lean_io_error_to_string(x_78);
if (lean_is_scalar(x_25)) {
 x_81 = lean_alloc_ctor(3, 1, 0);
} else {
 x_81 = x_25;
 lean_ctor_set_tag(x_81, 3);
}
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Lean_MessageData_ofFormat(x_81);
lean_inc(x_79);
lean_ctor_set(x_18, 1, x_82);
lean_ctor_set(x_18, 0, x_79);
lean_ctor_set(x_44, 0, x_18);
return x_44;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_44, 0);
lean_inc(x_83);
lean_dec(x_44);
x_84 = lean_ctor_get(x_40, 7);
x_85 = lean_io_error_to_string(x_83);
if (lean_is_scalar(x_25)) {
 x_86 = lean_alloc_ctor(3, 1, 0);
} else {
 x_86 = x_25;
 lean_ctor_set_tag(x_86, 3);
}
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_MessageData_ofFormat(x_86);
lean_inc(x_84);
lean_ctor_set(x_18, 1, x_87);
lean_ctor_set(x_18, 0, x_84);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_18);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_18);
x_89 = lean_ctor_get(x_44, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_90 = x_44;
} else {
 lean_dec_ref(x_44);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_40, 7);
x_92 = lean_io_error_to_string(x_89);
if (lean_is_scalar(x_25)) {
 x_93 = lean_alloc_ctor(3, 1, 0);
} else {
 x_93 = x_25;
 lean_ctor_set_tag(x_93, 3);
}
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
lean_inc(x_91);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_90;
}
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_36);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_25)) {
 x_122 = lean_alloc_ctor(0, 1, 0);
} else {
 x_122 = x_25;
 lean_ctor_set_tag(x_122, 0);
}
lean_ctor_set(x_122, 0, x_2);
return x_122;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_21);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_25)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_25;
 lean_ctor_set_tag(x_123, 0);
}
lean_ctor_set(x_123, 0, x_2);
return x_123;
}
}
else
{
lean_object* x_124; 
lean_dec(x_24);
lean_dec(x_21);
lean_free_object(x_16);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_25)) {
 x_124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_124 = x_25;
 lean_ctor_set_tag(x_124, 0);
}
lean_ctor_set(x_124, 0, x_2);
return x_124;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_16, 0);
lean_inc(x_125);
lean_dec(x_16);
x_126 = lean_st_ref_get(x_1);
x_127 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg(x_126, x_125);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_Elab_Info_stx(x_5);
x_129 = l_Lean_Syntax_getHeadInfo(x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
if (x_14 == 0)
{
lean_object* x_130; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_2);
return x_130;
}
else
{
lean_object* x_131; 
lean_inc(x_15);
lean_inc_ref(x_12);
x_131 = lean_local_ctx_find(x_12, x_15);
if (lean_obj_tag(x_131) == 1)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_125, 0);
x_135 = l_Lean_Syntax_Range_contains(x_3, x_134, x_127);
if (x_135 == 0)
{
lean_object* x_136; 
lean_dec(x_132);
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_133)) {
 x_136 = lean_alloc_ctor(0, 1, 0);
} else {
 x_136 = x_133;
 lean_ctor_set_tag(x_136, 0);
}
lean_ctor_set(x_136, 0, x_2);
return x_136;
}
else
{
if (x_127 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_LocalDecl_userName(x_132);
lean_dec(x_132);
x_138 = l_Lean_Name_hasMacroScopes(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_4, 0);
x_140 = lean_ctor_get(x_139, 4);
x_141 = l_Lean_Linter_linter_constructorNameAsVariable;
x_142 = l_Lean_Option_get___at___00Lean_Linter_constructorNameAsVariable_spec__1(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_133)) {
 x_143 = lean_alloc_ctor(0, 1, 0);
} else {
 x_143 = x_133;
 lean_ctor_set_tag(x_143, 0);
}
lean_ctor_set(x_143, 0, x_2);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = l_Lean_Syntax_getId(x_128);
lean_dec(x_128);
if (lean_obj_tag(x_144) == 1)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc_ref(x_146);
if (lean_obj_tag(x_145) == 0)
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_13, 0);
lean_inc(x_179);
x_147 = x_179;
x_148 = x_7;
x_149 = x_8;
x_150 = lean_box(0);
goto block_178;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_inc_ref(x_11);
x_180 = lean_alloc_closure((void*)(l_Lean_Meta_inferType___boxed), 6, 1);
lean_closure_set(x_180, 0, x_11);
lean_inc_ref(x_4);
lean_inc_ref(x_10);
x_181 = l_Lean_Elab_TermInfo_runMetaM___redArg(x_10, x_4, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_147 = x_182;
x_148 = x_7;
x_149 = x_8;
x_150 = lean_box(0);
goto block_178;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_146);
lean_dec_ref(x_144);
lean_dec(x_133);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_183 = x_125;
} else {
 lean_dec_ref(x_125);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_185 = x_181;
} else {
 lean_dec_ref(x_181);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_7, 7);
x_187 = lean_io_error_to_string(x_184);
x_188 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = l_Lean_MessageData_ofFormat(x_188);
lean_inc(x_186);
if (lean_is_scalar(x_183)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_183;
}
lean_ctor_set(x_190, 0, x_186);
lean_ctor_set(x_190, 1, x_189);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; 
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec_ref(x_144);
lean_dec(x_133);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_2);
return x_192;
}
block_178:
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__1___boxed), 6, 1);
lean_closure_set(x_151, 0, x_147);
lean_inc_ref(x_10);
x_152 = l_Lean_Elab_TermInfo_runMetaM___redArg(x_10, x_4, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = l_Lean_Expr_getAppFn_x27(x_153);
lean_dec(x_153);
if (lean_obj_tag(x_155) == 4)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = lean_st_ref_get(x_149);
x_158 = lean_ctor_get(x_157, 0);
lean_inc_ref(x_158);
lean_dec(x_157);
x_159 = l_Lean_Environment_find_x3f(x_158, x_156, x_138);
if (lean_obj_tag(x_159) == 1)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
if (lean_obj_tag(x_160) == 5)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_154);
x_161 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_161);
lean_dec_ref(x_160);
x_162 = lean_ctor_get(x_161, 4);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(x_146, x_1, x_5, x_144, x_125, x_138, x_162, x_2, x_149);
lean_dec_ref(x_5);
lean_dec_ref(x_146);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_164 = x_163;
} else {
 lean_dec_ref(x_163);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_2);
return x_165;
}
else
{
return x_163;
}
}
else
{
lean_object* x_166; 
lean_dec(x_160);
lean_dec_ref(x_146);
lean_dec_ref(x_144);
lean_dec(x_125);
lean_dec_ref(x_5);
if (lean_is_scalar(x_154)) {
 x_166 = lean_alloc_ctor(0, 1, 0);
} else {
 x_166 = x_154;
}
lean_ctor_set(x_166, 0, x_2);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_159);
lean_dec_ref(x_146);
lean_dec_ref(x_144);
lean_dec(x_125);
lean_dec_ref(x_5);
if (lean_is_scalar(x_154)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_154;
}
lean_ctor_set(x_167, 0, x_2);
return x_167;
}
}
else
{
lean_object* x_168; 
lean_dec_ref(x_155);
lean_dec_ref(x_146);
lean_dec_ref(x_144);
lean_dec(x_125);
lean_dec_ref(x_5);
if (lean_is_scalar(x_154)) {
 x_168 = lean_alloc_ctor(0, 1, 0);
} else {
 x_168 = x_154;
}
lean_ctor_set(x_168, 0, x_2);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec_ref(x_146);
lean_dec_ref(x_144);
lean_dec_ref(x_5);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_169 = x_125;
} else {
 lean_dec_ref(x_125);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_152, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_171 = x_152;
} else {
 lean_dec_ref(x_152);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_148, 7);
x_173 = lean_io_error_to_string(x_170);
if (lean_is_scalar(x_133)) {
 x_174 = lean_alloc_ctor(3, 1, 0);
} else {
 x_174 = x_133;
 lean_ctor_set_tag(x_174, 3);
}
lean_ctor_set(x_174, 0, x_173);
x_175 = l_Lean_MessageData_ofFormat(x_174);
lean_inc(x_172);
if (lean_is_scalar(x_169)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_169;
}
lean_ctor_set(x_176, 0, x_172);
lean_ctor_set(x_176, 1, x_175);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(1, 1, 0);
} else {
 x_177 = x_171;
}
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
}
else
{
lean_object* x_193; 
lean_dec(x_144);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_133)) {
 x_193 = lean_alloc_ctor(0, 1, 0);
} else {
 x_193 = x_133;
 lean_ctor_set_tag(x_193, 0);
}
lean_ctor_set(x_193, 0, x_2);
return x_193;
}
}
}
else
{
lean_object* x_194; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_133)) {
 x_194 = lean_alloc_ctor(0, 1, 0);
} else {
 x_194 = x_133;
 lean_ctor_set_tag(x_194, 0);
}
lean_ctor_set(x_194, 0, x_2);
return x_194;
}
}
else
{
lean_object* x_195; 
lean_dec(x_132);
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_133)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_133;
 lean_ctor_set_tag(x_195, 0);
}
lean_ctor_set(x_195, 0, x_2);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_131);
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_2);
return x_196;
}
}
}
else
{
lean_object* x_197; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_2);
return x_197;
}
}
else
{
lean_object* x_198; 
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_2);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_16);
lean_dec_ref(x_4);
x_199 = !lean_is_exclusive(x_5);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_5, 0);
lean_dec(x_200);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_201; 
lean_dec(x_5);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_2);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec_ref(x_4);
x_202 = !lean_is_exclusive(x_5);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_5, 0);
lean_dec(x_203);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_204; 
lean_dec(x_5);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_2);
return x_204;
}
}
}
else
{
lean_object* x_205; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_2);
return x_205;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__0;
x_6 = l_ReaderT_instMonad___redArg(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 2);
x_13 = lean_ctor_get(x_8, 3);
x_14 = lean_ctor_get(x_8, 4);
x_15 = lean_ctor_get(x_8, 1);
lean_dec(x_15);
x_16 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__1));
x_17 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__2));
lean_inc_ref(x_11);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_11);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_23, 0, x_12);
lean_ctor_set(x_8, 4, x_21);
lean_ctor_set(x_8, 3, x_22);
lean_ctor_set(x_8, 2, x_23);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_6, 1, x_17);
x_24 = lean_box(0);
x_25 = l_instInhabitedOfMonad___redArg(x_6, x_24);
x_26 = lean_panic_fn(x_25, x_1);
x_27 = lean_apply_3(x_26, x_2, x_3, lean_box(0));
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 2);
x_30 = lean_ctor_get(x_8, 3);
x_31 = lean_ctor_get(x_8, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_32 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__1));
x_33 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__2));
lean_inc_ref(x_28);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_28);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_30);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_39, 0, x_29);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_40);
x_41 = lean_box(0);
x_42 = l_instInhabitedOfMonad___redArg(x_6, x_41);
x_43 = lean_panic_fn(x_42, x_1);
x_44 = lean_apply_3(x_43, x_2, x_3, lean_box(0));
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
lean_dec(x_6);
x_46 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_45, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 4);
lean_inc(x_49);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 x_50 = x_45;
} else {
 lean_dec_ref(x_45);
 x_50 = lean_box(0);
}
x_51 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__1));
x_52 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__2));
lean_inc_ref(x_46);
x_53 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_53, 0, x_46);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_54, 0, x_46);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_57, 0, x_48);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_58, 0, x_47);
if (lean_is_scalar(x_50)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_50;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_57);
lean_ctor_set(x_59, 4, x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
x_61 = lean_box(0);
x_62 = l_instInhabitedOfMonad___redArg(x_60, x_61);
x_63 = lean_panic_fn(x_62, x_1);
x_64 = lean_apply_3(x_63, x_2, x_3, lean_box(0));
return x_64;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__2));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(65u);
x_4 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_4);
x_10 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_8, x_3);
x_3 = x_10;
x_4 = x_9;
goto _start;
}
case 1:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__3;
x_13 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg(x_12, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_16);
x_17 = lean_apply_6(x_1, x_16, x_14, x_15, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_apply_7(x_2, x_16, x_14, x_15, x_22, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_3, 0, x_25);
lean_ctor_set(x_23, 0, x_3);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_3, 0, x_26);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_3);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_3);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_apply_7(x_2, x_16, x_14, x_15, x_31, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Elab_Info_updateContext_x3f(x_3, x_14);
x_41 = l_Lean_PersistentArray_toList___redArg(x_15);
x_42 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_43 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg(x_1, x_2, x_40, x_41, x_42, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_apply_7(x_2, x_16, x_14, x_15, x_44, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
return x_43;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_17, 0);
lean_inc(x_59);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
default: 
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_4);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_4, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_63);
return x_4;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_4);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = l_List_reverse___redArg(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(x_1, x_2, x_3, x_12, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_15);
{
lean_object* _tmp_3 = x_13;
lean_object* _tmp_4 = x_4;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_22 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(x_1, x_2, x_3, x_20, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_4 = x_21;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_1, x_2, x_3, x_4, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__0(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_box(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__0___boxed), 7, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(0);
lean_inc_ref(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___lam__2___boxed), 9, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_2);
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
x_18 = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5(x_13, x_15, x_17, x_16, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
size_t x_19; size_t x_20; 
lean_dec_ref(x_18);
x_19 = 1;
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec_ref(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Syntax_getRange_x3f(x_1, x_5);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_st_ref_get(x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1;
x_11 = lean_st_mk_ref(x_10);
x_12 = lean_ctor_get(x_8, 8);
lean_inc_ref(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_PersistentArray_toArray___redArg(x_13);
lean_dec_ref(x_13);
x_15 = lean_box(0);
x_16 = lean_array_size(x_14);
x_17 = 0;
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_11);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__7(x_11, x_7, x_14, x_16, x_17, x_15, x_2, x_3);
lean_dec_ref(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_39; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec_ref(x_18);
x_19 = lean_st_ref_get(x_11);
lean_dec(x_11);
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_47);
lean_dec(x_19);
x_48 = lean_mk_empty_array_with_capacity(x_46);
lean_dec(x_46);
x_49 = lean_array_get_size(x_47);
x_50 = lean_nat_dec_lt(x_9, x_49);
if (x_50 == 0)
{
lean_dec_ref(x_47);
x_39 = x_48;
goto block_45;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_49, x_49);
if (x_51 == 0)
{
if (x_50 == 0)
{
lean_dec_ref(x_47);
x_39 = x_48;
goto block_45;
}
else
{
size_t x_52; lean_object* x_53; 
x_52 = lean_usize_of_nat(x_49);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11(x_47, x_17, x_52, x_48);
lean_dec_ref(x_47);
x_39 = x_53;
goto block_45;
}
}
else
{
size_t x_54; lean_object* x_55; 
x_54 = lean_usize_of_nat(x_49);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_constructorNameAsVariable_spec__11(x_47, x_17, x_54, x_48);
lean_dec_ref(x_47);
x_39 = x_55;
goto block_45;
}
}
block_26:
{
size_t x_21; lean_object* x_22; 
x_21 = lean_array_size(x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8(x_20, x_21, x_17, x_15, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
else
{
lean_object* x_25; 
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_15);
return x_25;
}
}
else
{
return x_22;
}
}
block_32:
{
lean_object* x_31; 
lean_dec(x_28);
x_31 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg(x_27, x_29, x_30);
lean_dec(x_30);
x_20 = x_31;
goto block_26;
}
block_38:
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_36, x_34);
if (x_37 == 0)
{
lean_dec(x_34);
lean_inc(x_36);
x_27 = x_33;
x_28 = x_35;
x_29 = x_36;
x_30 = x_36;
goto block_32;
}
else
{
x_27 = x_33;
x_28 = x_35;
x_29 = x_36;
x_30 = x_34;
goto block_32;
}
}
block_45:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_eq(x_40, x_9);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_40, x_42);
x_44 = lean_nat_dec_le(x_9, x_43);
if (x_44 == 0)
{
lean_inc(x_43);
x_33 = x_39;
x_34 = x_43;
x_35 = x_40;
x_36 = x_43;
goto block_38;
}
else
{
x_33 = x_39;
x_34 = x_43;
x_35 = x_40;
x_36 = x_9;
goto block_38;
}
}
else
{
x_20 = x_39;
goto block_26;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_constructorNameAsVariable___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_constructorNameAsVariable___lam__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
x_15 = l_List_forIn_x27_loop___at___00Lean_Linter_constructorNameAsVariable_spec__4(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_constructorNameAsVariable_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_constructorNameAsVariable_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_constructorNameAsVariable_spec__2_spec__3_spec__5_spec__14___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Linter_constructorNameAsVariable));
x_3 = l_Lean_Elab_Command_addLinter(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
return x_2;
}
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
l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_ = _init_l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_4011908533____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_constructorNameAsVariable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_constructorNameAsVariable);
lean_dec_ref(res);
}l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6_spec__10_spec__14_spec__21___redArg___closed__6);
l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1 = _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1();
lean_mark_persistent(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__1);
l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3 = _init_l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3();
lean_mark_persistent(l_Lean_Linter_logLint___at___00Lean_Linter_constructorNameAsVariable_spec__6___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__5);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__7);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__9);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_constructorNameAsVariable_spec__8___closed__11);
l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__0 = _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8_spec__10___redArg___closed__0);
l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__3 = _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__3();
lean_mark_persistent(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Linter_constructorNameAsVariable_spec__5_spec__8___redArg___closed__3);
l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0 = _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0();
lean_mark_persistent(l_Lean_Linter_constructorNameAsVariable___lam__0___closed__0);
l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1 = _init_l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1();
lean_mark_persistent(l_Lean_Linter_constructorNameAsVariable___lam__0___closed__1);
if (builtin) {res = l___private_Lean_Linter_ConstructorAsVariable_0__Lean_Linter_initFn_00___x40_Lean_Linter_ConstructorAsVariable_3137021433____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
