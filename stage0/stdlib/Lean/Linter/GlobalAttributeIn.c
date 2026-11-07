// Lean compiler output
// Module: Lean.Linter.GlobalAttributeIn
// Imports: public import Lean.Elab.Command public import Lean.Linter.Basic
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Syntax_isQuot(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_withSetOptionIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eraseAttr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 147, 124, 197, 194, 198, 27, 195)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(199, 36, 31, 135, 78, 131, 139, 152)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 79, 35, 19, 21, 38, 89, 10)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Despite the `in`, the attribute "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " is added globally to "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "\nplease remove the `in` or make this a `local "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0_value;
static const lean_closure_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_withSetOptionIn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__0_value)} };
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1_value;
static const lean_string_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__3_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4_value;
static const lean_string_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__4_value),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6_value;
static const lean_string_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "GlobalAttributeIn"};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__6_value),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__7_value),LEAN_SCALAR_PTR_LITERAL(1, 22, 223, 102, 44, 159, 140, 81)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(36, 117, 44, 116, 245, 145, 10, 240)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__9_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 78, 16, 194, 51, 19, 26, 37)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__10_value),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(71, 45, 189, 177, 125, 155, 239, 226)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11_value;
static const lean_string_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "globalAttributeIn"};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__11_value),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__12_value),LEAN_SCALAR_PTR_LITERAL(230, 74, 117, 23, 182, 33, 182, 250)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13_value;
static const lean_ctor_object l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__1_value),((lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__13_value)}};
static const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14 = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14_value;
LEAN_EXPORT const lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn = (const lean_object*)&l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot(lean_object* v_stx_1_){
_start:
{
lean_inc(v_stx_1_);
return v_stx_1_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot___boxed(lean_object* v_stx_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_topDownSkipQuot(v_stx_2_);
lean_dec(v_stx_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__0(lean_object* v_toPure_4_, lean_object* v_____r_5_, lean_object* v_b_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v_b_6_);
v___x_8_ = lean_apply_2(v_toPure_4_, lean_box(0), v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__1(lean_object* v___f_9_, lean_object* v_toPure_10_, lean_object* v_____s_11_){
_start:
{
lean_object* v_fst_12_; 
v_fst_12_ = lean_ctor_get(v_____s_11_, 0);
if (lean_obj_tag(v_fst_12_) == 0)
{
lean_object* v_snd_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_toPure_10_);
v_snd_13_ = lean_ctor_get(v_____s_11_, 1);
lean_inc(v_snd_13_);
lean_dec_ref(v_____s_11_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_apply_2(v___f_9_, v___x_14_, v_snd_13_);
return v___x_15_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_17_; 
lean_inc_ref(v_fst_12_);
lean_dec_ref(v_____s_11_);
lean_dec(v___f_9_);
v_val_16_ = lean_ctor_get(v_fst_12_, 0);
lean_inc(v_val_16_);
lean_dec_ref_known(v_fst_12_, 1);
v___x_17_ = lean_apply_2(v_toPure_10_, lean_box(0), v_val_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__2(lean_object* v_snd_18_, lean_object* v_toPure_19_, lean_object* v___x_20_, lean_object* v_____do__lift_21_){
_start:
{
if (lean_obj_tag(v_____do__lift_21_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_20_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v_____do__lift_21_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_snd_18_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
v___x_25_ = lean_apply_2(v_toPure_19_, lean_box(0), v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_35_; 
lean_dec(v_snd_18_);
v_a_26_ = lean_ctor_get(v_____do__lift_21_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v_____do__lift_21_);
if (v_isSharedCheck_35_ == 0)
{
v___x_28_ = v_____do__lift_21_;
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v_____do__lift_21_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_35_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_20_);
lean_ctor_set(v___x_30_, 1, v_a_26_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_30_);
v___x_32_ = v___x_28_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_34_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_2(v_toPure_19_, lean_box(0), v___x_32_);
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__4(lean_object* v_toPure_36_, lean_object* v_stx_37_, lean_object* v_inst_38_, lean_object* v_f_39_, lean_object* v_toBind_40_, lean_object* v___f_41_, lean_object* v___f_42_, lean_object* v_____do__lift_43_){
_start:
{
if (lean_obj_tag(v_____do__lift_43_) == 0)
{
lean_object* v___x_44_; 
lean_dec(v___f_42_);
lean_dec(v___f_41_);
lean_dec(v_toBind_40_);
lean_dec(v_f_39_);
lean_dec_ref(v_inst_38_);
lean_dec(v_stx_37_);
v___x_44_ = lean_apply_2(v_toPure_36_, lean_box(0), v_____do__lift_43_);
return v___x_44_;
}
else
{
if (lean_obj_tag(v_stx_37_) == 1)
{
lean_object* v_a_45_; lean_object* v_args_46_; lean_object* v___x_47_; lean_object* v___f_48_; lean_object* v___x_49_; size_t v_sz_50_; size_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_dec(v___f_42_);
v_a_45_ = lean_ctor_get(v_____do__lift_43_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v_____do__lift_43_, 1);
v_args_46_ = lean_ctor_get(v_stx_37_, 2);
lean_inc_ref(v_args_46_);
lean_dec_ref_known(v_stx_37_, 3);
v___x_47_ = lean_box(0);
lean_inc(v_toBind_40_);
lean_inc_ref(v_inst_38_);
v___f_48_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__3), 8, 5);
lean_closure_set(v___f_48_, 0, v_toPure_36_);
lean_closure_set(v___f_48_, 1, v___x_47_);
lean_closure_set(v___f_48_, 2, v_inst_38_);
lean_closure_set(v___f_48_, 3, v_f_39_);
lean_closure_set(v___f_48_, 4, v_toBind_40_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_47_);
lean_ctor_set(v___x_49_, 1, v_a_45_);
v_sz_50_ = lean_array_size(v_args_46_);
v___x_51_ = ((size_t)0ULL);
v___x_52_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_38_, v_args_46_, v___f_48_, v_sz_50_, v___x_51_, v___x_49_);
v___x_53_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v___x_52_, v___f_41_);
return v___x_53_;
}
else
{
lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v___f_41_);
lean_dec(v_toBind_40_);
lean_dec(v_f_39_);
lean_dec_ref(v_inst_38_);
lean_dec(v_stx_37_);
lean_dec(v_toPure_36_);
v_a_54_ = lean_ctor_get(v_____do__lift_43_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v_____do__lift_43_, 1);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_2(v___f_42_, v___x_55_, v_a_54_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(lean_object* v_inst_57_, lean_object* v_f_58_, lean_object* v_stx_59_, lean_object* v_b_60_){
_start:
{
lean_object* v_toApplicative_61_; lean_object* v_toBind_62_; lean_object* v_toPure_63_; uint8_t v___x_64_; 
v_toApplicative_61_ = lean_ctor_get(v_inst_57_, 0);
v_toBind_62_ = lean_ctor_get(v_inst_57_, 1);
lean_inc(v_toBind_62_);
v_toPure_63_ = lean_ctor_get(v_toApplicative_61_, 1);
lean_inc(v_toPure_63_);
v___x_64_ = l_Lean_Syntax_isQuot(v_stx_59_);
if (v___x_64_ == 0)
{
lean_object* v___f_65_; lean_object* v___f_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc_n(v_toPure_63_, 2);
v___f_65_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_65_, 0, v_toPure_63_);
lean_inc_ref(v___f_65_);
v___f_66_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_66_, 0, v___f_65_);
lean_closure_set(v___f_66_, 1, v_toPure_63_);
lean_inc(v_toBind_62_);
lean_inc(v_f_58_);
lean_inc(v_stx_59_);
v___f_67_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__4), 8, 7);
lean_closure_set(v___f_67_, 0, v_toPure_63_);
lean_closure_set(v___f_67_, 1, v_stx_59_);
lean_closure_set(v___f_67_, 2, v_inst_57_);
lean_closure_set(v___f_67_, 3, v_f_58_);
lean_closure_set(v___f_67_, 4, v_toBind_62_);
lean_closure_set(v___f_67_, 5, v___f_66_);
lean_closure_set(v___f_67_, 6, v___f_65_);
v___x_68_ = lean_apply_2(v_f_58_, v_stx_59_, v_b_60_);
v___x_69_ = lean_apply_4(v_toBind_62_, lean_box(0), lean_box(0), v___x_68_, v___f_67_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_toBind_62_);
lean_dec(v_stx_59_);
lean_dec(v_f_58_);
lean_dec_ref(v_inst_57_);
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v_b_60_);
v___x_71_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__3(lean_object* v_toPure_72_, lean_object* v___x_73_, lean_object* v_inst_74_, lean_object* v_f_75_, lean_object* v_toBind_76_, lean_object* v_a_77_, lean_object* v_x_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_snd_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v_snd_80_ = lean_ctor_get(v___y_79_, 1);
lean_inc_n(v_snd_80_, 2);
lean_dec_ref(v___y_79_);
v___f_81_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_81_, 0, v_snd_80_);
lean_closure_set(v___f_81_, 1, v_toPure_72_);
lean_closure_set(v___f_81_, 2, v___x_73_);
v___x_82_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(v_inst_74_, v_f_75_, v_a_77_, v_snd_80_);
v___x_83_ = lean_apply_4(v_toBind_76_, lean_box(0), lean_box(0), v___x_82_, v___f_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop(lean_object* v_m_84_, lean_object* v_inst_85_, lean_object* v_00_u03b2_86_, lean_object* v_f_87_, lean_object* v_stx_88_, lean_object* v_b_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(v_inst_85_, v_f_87_, v_stx_88_, v_b_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___boxed(lean_object* v_m_92_, lean_object* v_inst_93_, lean_object* v_00_u03b2_94_, lean_object* v_f_95_, lean_object* v_stx_96_, lean_object* v_b_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop(v_m_92_, v_inst_93_, v_00_u03b2_94_, v_f_95_, v_stx_96_, v_b_97_, v_inst_98_);
lean_dec(v_inst_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__0(lean_object* v_toPure_100_, lean_object* v_____do__lift_101_){
_start:
{
lean_object* v_a_102_; lean_object* v___x_103_; 
v_a_102_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v_____do__lift_101_);
v___x_103_ = lean_apply_2(v_toPure_100_, lean_box(0), v_a_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__1(lean_object* v_inst_104_, lean_object* v_toBind_105_, lean_object* v___f_106_, lean_object* v_00_u03b2_107_, lean_object* v_x_108_, lean_object* v_init_109_, lean_object* v_f_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___redArg(v_inst_104_, v_f_110_, v_x_108_, v_init_109_);
v___x_112_ = lean_apply_4(v_toBind_105_, lean_box(0), lean_box(0), v___x_111_, v___f_106_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg(lean_object* v_inst_113_){
_start:
{
lean_object* v_toApplicative_114_; lean_object* v_toBind_115_; lean_object* v_toPure_116_; lean_object* v___f_117_; lean_object* v___f_118_; 
v_toApplicative_114_ = lean_ctor_get(v_inst_113_, 0);
v_toBind_115_ = lean_ctor_get(v_inst_113_, 1);
lean_inc(v_toBind_115_);
v_toPure_116_ = lean_ctor_get(v_toApplicative_114_, 1);
lean_inc(v_toPure_116_);
v___f_117_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_117_, 0, v_toPure_116_);
v___f_118_ = lean_alloc_closure((void*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_118_, 0, v_inst_113_);
lean_closure_set(v___f_118_, 1, v_toBind_115_);
lean_closure_set(v___f_118_, 2, v___f_117_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad(lean_object* v_m_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad___redArg(v_inst_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(lean_object* v_as_156_, size_t v_i_157_, size_t v_stop_158_, lean_object* v_b_159_){
_start:
{
lean_object* v___y_161_; uint8_t v___x_165_; 
v___x_165_ = lean_usize_dec_eq(v_i_157_, v_stop_158_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v_a_167_; uint8_t v___x_168_; 
v___x_166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__4));
v_a_167_ = lean_array_uget_borrowed(v_as_156_, v_i_157_);
lean_inc(v_a_167_);
v___x_168_ = l_Lean_Syntax_isOfKind(v_a_167_, v___x_166_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__7));
lean_inc(v_a_167_);
v___x_170_ = l_Lean_Syntax_isOfKind(v_a_167_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
lean_inc(v_a_167_);
v___x_171_ = lean_array_push(v_b_159_, v_a_167_);
v___y_161_ = v___x_171_;
goto v___jp_160_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = l_Lean_Syntax_getArg(v_a_167_, v___x_172_);
v___x_174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__9));
lean_inc(v___x_173_);
v___x_175_ = l_Lean_Syntax_isOfKind(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v___x_173_);
lean_inc(v_a_167_);
v___x_176_ = lean_array_push(v_b_159_, v_a_167_);
v___y_161_ = v___x_176_;
goto v___jp_160_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = l_Lean_Syntax_getArg(v___x_173_, v___x_172_);
lean_dec(v___x_173_);
lean_inc(v___x_178_);
v___x_179_ = l_Lean_Syntax_matchesNull(v___x_178_, v___x_177_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_dec(v___x_178_);
lean_inc(v_a_167_);
v___x_180_ = lean_array_push(v_b_159_, v_a_167_);
v___y_161_ = v___x_180_;
goto v___jp_160_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Lean_Syntax_getArg(v___x_178_, v___x_172_);
lean_dec(v___x_178_);
v___x_182_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__11));
lean_inc(v___x_181_);
v___x_183_ = l_Lean_Syntax_isOfKind(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___closed__13));
v___x_185_ = l_Lean_Syntax_isOfKind(v___x_181_, v___x_184_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_inc(v_a_167_);
v___x_186_ = lean_array_push(v_b_159_, v_a_167_);
v___y_161_ = v___x_186_;
goto v___jp_160_;
}
else
{
v___y_161_ = v_b_159_;
goto v___jp_160_;
}
}
else
{
lean_dec(v___x_181_);
v___y_161_ = v_b_159_;
goto v___jp_160_;
}
}
}
}
}
else
{
v___y_161_ = v_b_159_;
goto v___jp_160_;
}
}
else
{
return v_b_159_;
}
v___jp_160_:
{
size_t v___x_162_; size_t v___x_163_; 
v___x_162_ = ((size_t)1ULL);
v___x_163_ = lean_usize_add(v_i_157_, v___x_162_);
v_i_157_ = v___x_163_;
v_b_159_ = v___y_161_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0___boxed(lean_object* v_as_187_, lean_object* v_i_188_, lean_object* v_stop_189_, lean_object* v_b_190_){
_start:
{
size_t v_i_boxed_191_; size_t v_stop_boxed_192_; lean_object* v_res_193_; 
v_i_boxed_191_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_stop_boxed_192_ = lean_unbox_usize(v_stop_189_);
lean_dec(v_stop_189_);
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(v_as_187_, v_i_boxed_191_, v_stop_boxed_192_, v_b_190_);
lean_dec_ref(v_as_187_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(lean_object* v_as_196_, lean_object* v_start_197_, lean_object* v_stop_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___closed__0));
v___x_200_ = lean_nat_dec_lt(v_start_197_, v_stop_198_);
if (v___x_200_ == 0)
{
return v___x_199_;
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_array_get_size(v_as_196_);
v___x_202_ = lean_nat_dec_le(v_stop_198_, v___x_201_);
if (v___x_202_ == 0)
{
uint8_t v___x_203_; 
v___x_203_ = lean_nat_dec_lt(v_start_197_, v___x_201_);
if (v___x_203_ == 0)
{
return v___x_199_;
}
else
{
size_t v___x_204_; size_t v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_usize_of_nat(v_start_197_);
v___x_205_ = lean_usize_of_nat(v___x_201_);
v___x_206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(v_as_196_, v___x_204_, v___x_205_, v___x_199_);
return v___x_206_;
}
}
else
{
size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_usize_of_nat(v_start_197_);
v___x_208_ = lean_usize_of_nat(v_stop_198_);
v___x_209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0_spec__0(v_as_196_, v___x_207_, v___x_208_, v___x_199_);
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0___boxed(lean_object* v_as_210_, lean_object* v_start_211_, lean_object* v_stop_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(v_as_210_, v_start_211_, v_stop_212_);
lean_dec(v_stop_212_);
lean_dec(v_start_211_);
lean_dec_ref(v_as_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f(lean_object* v_x_226_){
_start:
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = ((lean_object*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__1));
lean_inc(v_x_226_);
v___x_228_ = l_Lean_Syntax_isOfKind(v_x_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
lean_dec(v_x_226_);
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_Syntax_getArg(v_x_226_, v___x_230_);
lean_dec(v_x_226_);
v___x_232_ = ((lean_object*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f___closed__3));
lean_inc(v___x_231_);
v___x_233_ = l_Lean_Syntax_isOfKind(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
return v___x_234_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_unsigned_to_nat(4u);
v___x_237_ = l_Lean_Syntax_getArg(v___x_231_, v___x_236_);
lean_inc(v___x_237_);
v___x_238_ = l_Lean_Syntax_matchesNull(v___x_237_, v___x_235_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v___x_237_);
lean_dec(v___x_231_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_id_242_; lean_object* v_x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_xs_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_240_ = lean_unsigned_to_nat(2u);
v___x_241_ = l_Lean_Syntax_getArg(v___x_231_, v___x_240_);
lean_dec(v___x_231_);
v_id_242_ = l_Lean_Syntax_getArg(v___x_237_, v___x_230_);
lean_dec(v___x_237_);
v_x_243_ = l_Lean_Syntax_getArgs(v___x_241_);
lean_dec(v___x_241_);
v___x_244_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_x_243_);
lean_dec_ref(v_x_243_);
v___x_245_ = lean_array_get_size(v___x_244_);
v_xs_246_ = l_Array_filterMapM___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f_spec__0(v___x_244_, v___x_230_, v___x_245_);
lean_dec_ref(v___x_244_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_id_242_);
lean_ctor_set(v___x_247_, 1, v_xs_246_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
}
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_249_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_ctor_set(v___x_254_, 2, v___x_253_);
lean_ctor_set(v___x_254_, 3, v___x_253_);
lean_ctor_set(v___x_254_, 4, v___x_252_);
lean_ctor_set(v___x_254_, 5, v___x_252_);
lean_ctor_set(v___x_254_, 6, v___x_252_);
lean_ctor_set(v___x_254_, 7, v___x_252_);
lean_ctor_set(v___x_254_, 8, v___x_252_);
lean_ctor_set(v___x_254_, 9, v___x_252_);
lean_ctor_set(v___x_254_, 10, v___x_252_);
return v___x_254_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(32u);
v___x_256_ = lean_mk_empty_array_with_capacity(v___x_255_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4(void){
_start:
{
size_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_258_ = ((size_t)5ULL);
v___x_259_ = lean_unsigned_to_nat(0u);
v___x_260_ = lean_unsigned_to_nat(32u);
v___x_261_ = lean_mk_empty_array_with_capacity(v___x_260_);
v___x_262_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_263_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_259_);
lean_ctor_set(v___x_263_, 3, v___x_259_);
lean_ctor_set_usize(v___x_263_, 4, v___x_258_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = lean_box(1);
v___x_265_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__4);
v___x_266_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; lean_object* v_env_272_; uint8_t v___x_273_; lean_object* v_env_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_scopes_277_; lean_object* v___x_278_; lean_object* v_opts_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_271_ = lean_st_ref_get(v___y_269_);
v_env_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_env_272_);
lean_dec(v___x_271_);
v___x_273_ = 0;
v_env_274_ = l_Lean_Environment_setRecordingDeps(v_env_272_, v___x_273_);
v___x_275_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_276_ = lean_st_ref_get(v___y_269_);
v_scopes_277_ = lean_ctor_get(v___x_276_, 2);
lean_inc(v_scopes_277_);
lean_dec(v___x_276_);
v___x_278_ = l_List_head_x21___redArg(v___x_275_, v_scopes_277_);
lean_dec(v_scopes_277_);
v_opts_279_ = lean_ctor_get(v___x_278_, 1);
lean_inc_ref(v_opts_279_);
lean_dec(v___x_278_);
v___x_280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_281_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_282_, 0, v_env_274_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_ctor_set(v___x_282_, 3, v_opts_279_);
v___x_283_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_msgData_268_);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v_msgData_285_, v___y_286_);
lean_dec(v___y_286_);
return v_res_288_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(lean_object* v_opts_289_, lean_object* v_opt_290_){
_start:
{
lean_object* v_name_291_; lean_object* v_defValue_292_; lean_object* v_map_293_; lean_object* v___x_294_; 
v_name_291_ = lean_ctor_get(v_opt_290_, 0);
v_defValue_292_ = lean_ctor_get(v_opt_290_, 1);
v_map_293_ = lean_ctor_get(v_opts_289_, 0);
v___x_294_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_293_, v_name_291_);
if (lean_obj_tag(v___x_294_) == 0)
{
uint8_t v___x_295_; 
v___x_295_ = lean_unbox(v_defValue_292_);
return v___x_295_;
}
else
{
lean_object* v_val_296_; 
v_val_296_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_val_296_);
lean_dec_ref_known(v___x_294_, 1);
if (lean_obj_tag(v_val_296_) == 1)
{
uint8_t v_v_297_; 
v_v_297_ = lean_ctor_get_uint8(v_val_296_, 0);
lean_dec_ref_known(v_val_296_, 0);
return v_v_297_;
}
else
{
uint8_t v___x_298_; 
lean_dec(v_val_296_);
v___x_298_ = lean_unbox(v_defValue_292_);
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_299_, lean_object* v_opt_300_){
_start:
{
uint8_t v_res_301_; lean_object* v_r_302_; 
v_res_301_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(v_opts_299_, v_opt_300_);
lean_dec_ref(v_opt_300_);
lean_dec_ref(v_opts_299_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 1)
{
lean_object* v_pre_306_; 
v_pre_306_ = lean_ctor_get(v_x_305_, 0);
if (lean_obj_tag(v_pre_306_) == 0)
{
lean_object* v_str_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v_str_307_ = lean_ctor_get(v_x_305_, 1);
v___x_308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0));
v___x_309_ = lean_string_dec_eq(v_str_307_, v___x_308_);
if (v___x_309_ == 0)
{
return v___x_309_;
}
else
{
return v_suppressElabErrors_304_;
}
}
else
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
}
else
{
uint8_t v___x_311_; 
v___x_311_ = 0;
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_312_, lean_object* v_x_313_){
_start:
{
uint8_t v_suppressElabErrors_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_suppressElabErrors_boxed_314_ = lean_unbox(v_suppressElabErrors_312_);
v_res_315_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_314_, v_x_313_);
lean_dec(v_x_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(lean_object* v_ref_318_, lean_object* v_msgData_319_, uint8_t v_severity_320_, uint8_t v_isSilent_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___y_328_; uint8_t v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_391_; uint8_t v___y_392_; uint8_t v___y_393_; lean_object* v___y_394_; lean_object* v___y_417_; uint8_t v___y_418_; uint8_t v___y_419_; lean_object* v___y_420_; uint8_t v___y_424_; uint8_t v___y_425_; uint8_t v___x_440_; uint8_t v___y_442_; uint8_t v___x_452_; 
v___x_440_ = 2;
v___x_452_ = l_Lean_instBEqMessageSeverity_beq(v_severity_320_, v___x_440_);
if (v___x_452_ == 0)
{
v___y_442_ = v___x_452_;
goto v___jp_441_;
}
else
{
uint8_t v___x_453_; 
lean_inc_ref(v_msgData_319_);
v___x_453_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_319_);
if (v___x_453_ == 0)
{
v___y_442_ = v___x_453_;
goto v___jp_441_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec_ref(v_msgData_319_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
v___jp_325_:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Elab_Command_getScope___redArg(v___y_333_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v_currNamespace_336_; lean_object* v___x_337_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v_currNamespace_336_ = lean_ctor_get(v_a_335_, 2);
lean_inc(v_currNamespace_336_);
lean_dec(v_a_335_);
v___x_337_ = l_Lean_Elab_Command_getScope___redArg(v___y_333_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_373_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_373_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_373_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_373_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_openDecls_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v_messages_348_; lean_object* v_scopes_349_; lean_object* v_usedQuotCtxts_350_; lean_object* v_nextMacroScope_351_; lean_object* v_maxRecDepth_352_; lean_object* v_ngen_353_; lean_object* v_auxDeclNGen_354_; lean_object* v_infoState_355_; lean_object* v_traceState_356_; lean_object* v_snapshotTasks_357_; lean_object* v_prevLinterStates_358_; lean_object* v_codeQualityEntryTasks_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_372_; 
v_openDecls_342_ = lean_ctor_get(v_a_338_, 3);
lean_inc(v_openDecls_342_);
lean_dec(v_a_338_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v_currNamespace_336_);
lean_ctor_set(v___x_343_, 1, v_openDecls_342_);
v___x_344_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___y_327_);
lean_inc_ref(v___y_330_);
lean_inc_ref(v___y_332_);
v___x_345_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_345_, 0, v___y_332_);
lean_ctor_set(v___x_345_, 1, v___y_328_);
lean_ctor_set(v___x_345_, 2, v___y_326_);
lean_ctor_set(v___x_345_, 3, v___y_330_);
lean_ctor_set(v___x_345_, 4, v___x_344_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*5, v___y_329_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*5 + 1, v___y_331_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*5 + 2, v_isSilent_321_);
v___x_346_ = lean_st_ref_take(v___y_333_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
v_messages_348_ = lean_ctor_get(v___x_346_, 1);
v_scopes_349_ = lean_ctor_get(v___x_346_, 2);
v_usedQuotCtxts_350_ = lean_ctor_get(v___x_346_, 3);
v_nextMacroScope_351_ = lean_ctor_get(v___x_346_, 4);
v_maxRecDepth_352_ = lean_ctor_get(v___x_346_, 5);
v_ngen_353_ = lean_ctor_get(v___x_346_, 6);
v_auxDeclNGen_354_ = lean_ctor_get(v___x_346_, 7);
v_infoState_355_ = lean_ctor_get(v___x_346_, 8);
v_traceState_356_ = lean_ctor_get(v___x_346_, 9);
v_snapshotTasks_357_ = lean_ctor_get(v___x_346_, 10);
v_prevLinterStates_358_ = lean_ctor_get(v___x_346_, 11);
v_codeQualityEntryTasks_359_ = lean_ctor_get(v___x_346_, 12);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_372_ == 0)
{
v___x_361_ = v___x_346_;
v_isShared_362_ = v_isSharedCheck_372_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_codeQualityEntryTasks_359_);
lean_inc(v_prevLinterStates_358_);
lean_inc(v_snapshotTasks_357_);
lean_inc(v_traceState_356_);
lean_inc(v_infoState_355_);
lean_inc(v_auxDeclNGen_354_);
lean_inc(v_ngen_353_);
lean_inc(v_maxRecDepth_352_);
lean_inc(v_nextMacroScope_351_);
lean_inc(v_usedQuotCtxts_350_);
lean_inc(v_scopes_349_);
lean_inc(v_messages_348_);
lean_inc(v_env_347_);
lean_dec(v___x_346_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_372_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_box(0);
v___x_364_ = l_Lean_MessageLog_add(v___x_345_, v_messages_348_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 1, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_env_347_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_scopes_349_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_usedQuotCtxts_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_nextMacroScope_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v_maxRecDepth_352_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_ngen_353_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_auxDeclNGen_354_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_371_, 9, v_traceState_356_);
lean_ctor_set(v_reuseFailAlloc_371_, 10, v_snapshotTasks_357_);
lean_ctor_set(v_reuseFailAlloc_371_, 11, v_prevLinterStates_358_);
lean_ctor_set(v_reuseFailAlloc_371_, 12, v_codeQualityEntryTasks_359_);
v___x_366_ = v_reuseFailAlloc_371_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_st_ref_put(v___y_333_, v___x_366_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_363_);
v___x_369_ = v___x_340_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_363_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_currNamespace_336_);
lean_dec_ref(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
v_a_374_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_337_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_337_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec_ref(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
v_a_382_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_334_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_334_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
v___jp_390_:
{
lean_object* v_fileName_395_; lean_object* v_fileMap_396_; uint8_t v_suppressElabErrors_397_; lean_object* v___x_398_; lean_object* v___f_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_415_; 
v_fileName_395_ = lean_ctor_get(v___y_322_, 0);
v_fileMap_396_ = lean_ctor_get(v___y_322_, 1);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_322_, sizeof(void*)*10);
v___x_398_ = lean_box(v_suppressElabErrors_397_);
v___f_399_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_399_, 0, v___x_398_);
v___x_400_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_319_);
v___x_401_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v___x_400_, v___y_323_);
v_a_402_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_415_ == 0)
{
v___x_404_ = v___x_401_;
v_isShared_405_ = v_isSharedCheck_415_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_401_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_415_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc_ref_n(v_fileMap_396_, 2);
v___x_406_ = l_Lean_FileMap_toPosition(v_fileMap_396_, v___y_391_);
lean_dec(v___y_391_);
v___x_407_ = l_Lean_FileMap_toPosition(v_fileMap_396_, v___y_394_);
lean_dec(v___y_394_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
v___x_409_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0));
if (v_suppressElabErrors_397_ == 0)
{
lean_del_object(v___x_404_);
lean_dec_ref(v___f_399_);
v___y_326_ = v___x_408_;
v___y_327_ = v_a_402_;
v___y_328_ = v___x_406_;
v___y_329_ = v___y_392_;
v___y_330_ = v___x_409_;
v___y_331_ = v___y_393_;
v___y_332_ = v_fileName_395_;
v___y_333_ = v___y_323_;
goto v___jp_325_;
}
else
{
uint8_t v___x_410_; 
lean_inc(v_a_402_);
v___x_410_ = l_Lean_MessageData_hasTag(v___f_399_, v_a_402_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_dec_ref_known(v___x_408_, 1);
lean_dec_ref(v___x_406_);
lean_dec(v_a_402_);
v___x_411_ = lean_box(0);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_411_);
v___x_413_ = v___x_404_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
else
{
lean_del_object(v___x_404_);
v___y_326_ = v___x_408_;
v___y_327_ = v_a_402_;
v___y_328_ = v___x_406_;
v___y_329_ = v___y_392_;
v___y_330_ = v___x_409_;
v___y_331_ = v___y_393_;
v___y_332_ = v_fileName_395_;
v___y_333_ = v___y_323_;
goto v___jp_325_;
}
}
}
}
v___jp_416_:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Syntax_getTailPos_x3f(v___y_417_, v___y_418_);
lean_dec(v___y_417_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_inc(v___y_420_);
v___y_391_ = v___y_420_;
v___y_392_ = v___y_418_;
v___y_393_ = v___y_419_;
v___y_394_ = v___y_420_;
goto v___jp_390_;
}
else
{
lean_object* v_val_422_; 
v_val_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_421_, 1);
v___y_391_ = v___y_420_;
v___y_392_ = v___y_418_;
v___y_393_ = v___y_419_;
v___y_394_ = v_val_422_;
goto v___jp_390_;
}
}
v___jp_423_:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Elab_Command_getRef___redArg(v___y_322_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v_ref_428_; lean_object* v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v_ref_428_ = l_Lean_replaceRef(v_ref_318_, v_a_427_);
lean_dec(v_a_427_);
v___x_429_ = l_Lean_Syntax_getPos_x3f(v_ref_428_, v___y_424_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_unsigned_to_nat(0u);
v___y_417_ = v_ref_428_;
v___y_418_ = v___y_424_;
v___y_419_ = v___y_425_;
v___y_420_ = v___x_430_;
goto v___jp_416_;
}
else
{
lean_object* v_val_431_; 
v_val_431_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_val_431_);
lean_dec_ref_known(v___x_429_, 1);
v___y_417_ = v_ref_428_;
v___y_418_ = v___y_424_;
v___y_419_ = v___y_425_;
v___y_420_ = v_val_431_;
goto v___jp_416_;
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec_ref(v_msgData_319_);
v_a_432_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_426_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_426_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_scopes_445_; lean_object* v___x_446_; lean_object* v_opts_447_; uint8_t v___x_448_; uint8_t v___x_449_; 
v___x_443_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_444_ = lean_st_ref_get(v___y_323_);
v_scopes_445_ = lean_ctor_get(v___x_444_, 2);
lean_inc(v_scopes_445_);
lean_dec(v___x_444_);
v___x_446_ = l_List_head_x21___redArg(v___x_443_, v_scopes_445_);
lean_dec(v_scopes_445_);
v_opts_447_ = lean_ctor_get(v___x_446_, 1);
lean_inc_ref(v_opts_447_);
lean_dec(v___x_446_);
v___x_448_ = 1;
v___x_449_ = l_Lean_instBEqMessageSeverity_beq(v_severity_320_, v___x_448_);
if (v___x_449_ == 0)
{
lean_dec_ref(v_opts_447_);
v___y_424_ = v___y_442_;
v___y_425_ = v_severity_320_;
goto v___jp_423_;
}
else
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = l_Lean_warningAsError;
v___x_451_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(v_opts_447_, v___x_450_);
lean_dec_ref(v_opts_447_);
if (v___x_451_ == 0)
{
v___y_424_ = v___y_442_;
v___y_425_ = v_severity_320_;
goto v___jp_423_;
}
else
{
v___y_424_ = v___y_442_;
v___y_425_ = v___x_440_;
goto v___jp_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___boxed(lean_object* v_ref_456_, lean_object* v_msgData_457_, lean_object* v_severity_458_, lean_object* v_isSilent_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
uint8_t v_severity_boxed_463_; uint8_t v_isSilent_boxed_464_; lean_object* v_res_465_; 
v_severity_boxed_463_ = lean_unbox(v_severity_458_);
v_isSilent_boxed_464_ = lean_unbox(v_isSilent_459_);
v_res_465_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(v_ref_456_, v_msgData_457_, v_severity_boxed_463_, v_isSilent_boxed_464_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v_ref_456_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(lean_object* v_ref_466_, lean_object* v_msgData_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
uint8_t v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = 2;
v___x_472_ = 0;
v___x_473_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(v_ref_466_, v_msgData_467_, v___x_471_, v___x_472_, v___y_468_, v___y_469_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0___boxed(lean_object* v_ref_474_, lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(v_ref_474_, v_msgData_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v_ref_474_);
return v_res_479_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0));
v___x_482_ = l_Lean_stringToMessageData(v___x_481_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(lean_object* v_fst_492_, lean_object* v_as_493_, size_t v_sz_494_, size_t v_i_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_lt(v_i_495_, v_sz_494_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec(v_fst_492_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_b_496_);
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_502_ = lean_box(0);
v_a_503_ = lean_array_uget_borrowed(v_as_493_, v_i_495_);
v___x_504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1);
lean_inc(v_a_503_);
v___x_505_ = l_Lean_MessageData_ofSyntax(v_a_503_);
lean_inc_ref(v___x_505_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
lean_inc(v_fst_492_);
v___x_509_ = l_Lean_MessageData_ofSyntax(v_fst_492_);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v___x_505_);
v___x_514_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(v_a_503_, v___x_515_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_516_) == 0)
{
size_t v___x_517_; size_t v___x_518_; 
lean_dec_ref_known(v___x_516_, 1);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_495_, v___x_517_);
v_i_495_ = v___x_518_;
v_b_496_ = v___x_502_;
goto _start;
}
else
{
lean_dec(v_fst_492_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___boxed(lean_object* v_fst_520_, lean_object* v_as_521_, lean_object* v_sz_522_, lean_object* v_i_523_, lean_object* v_b_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_522_);
lean_dec(v_sz_522_);
v_i_boxed_529_ = lean_unbox_usize(v_i_523_);
lean_dec(v_i_523_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(v_fst_520_, v_as_521_, v_sz_boxed_528_, v_i_boxed_529_, v_b_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec_ref(v_as_521_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(lean_object* v_stx_531_, lean_object* v_b_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_b_537_; lean_object* v_a_541_; uint8_t v___x_567_; 
v___x_567_ = l_Lean_Syntax_isQuot(v_stx_531_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_box(0);
lean_inc(v_stx_531_);
v___x_569_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f(v_stx_531_);
if (lean_obj_tag(v___x_569_) == 1)
{
lean_object* v_val_570_; lean_object* v_fst_571_; lean_object* v_snd_572_; size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_val_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v___x_569_, 1);
v_fst_571_ = lean_ctor_get(v_val_570_, 0);
lean_inc(v_fst_571_);
v_snd_572_ = lean_ctor_get(v_val_570_, 1);
lean_inc(v_snd_572_);
lean_dec(v_val_570_);
v_sz_573_ = lean_array_size(v_snd_572_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(v_fst_571_, v_snd_572_, v_sz_573_, v___x_574_, v___x_568_, v___y_533_, v___y_534_);
lean_dec(v_snd_572_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_dec_ref_known(v___x_575_, 1);
v_a_541_ = v___x_568_;
goto v___jp_540_;
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_stx_531_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_dec(v___x_569_);
v_a_541_ = v___x_568_;
goto v___jp_540_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_stx_531_);
v___x_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_584_, 0, v_b_532_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v_b_537_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
v___jp_540_:
{
if (lean_obj_tag(v_stx_531_) == 1)
{
lean_object* v_args_542_; lean_object* v___x_543_; lean_object* v___x_544_; size_t v_sz_545_; size_t v___x_546_; lean_object* v___x_547_; 
v_args_542_ = lean_ctor_get(v_stx_531_, 2);
lean_inc_ref(v_args_542_);
lean_dec_ref_known(v_stx_531_, 3);
v___x_543_ = lean_box(0);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set(v___x_544_, 1, v_a_541_);
v_sz_545_ = lean_array_size(v_args_542_);
v___x_546_ = ((size_t)0ULL);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(v_args_542_, v_sz_545_, v___x_546_, v___x_544_, v___y_533_, v___y_534_);
lean_dec_ref(v_args_542_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_558_ == 0)
{
v___x_550_ = v___x_547_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_547_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_fst_552_; 
v_fst_552_ = lean_ctor_get(v_a_548_, 0);
if (lean_obj_tag(v_fst_552_) == 0)
{
lean_object* v_snd_553_; 
lean_del_object(v___x_550_);
v_snd_553_ = lean_ctor_get(v_a_548_, 1);
lean_inc(v_snd_553_);
lean_dec(v_a_548_);
v_b_537_ = v_snd_553_;
goto v___jp_536_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_556_; 
lean_inc_ref(v_fst_552_);
lean_dec(v_a_548_);
v_val_554_ = lean_ctor_get(v_fst_552_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v_fst_552_, 1);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v_val_554_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_val_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_547_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_547_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
else
{
lean_dec(v_stx_531_);
v_b_537_ = v_a_541_;
goto v___jp_536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(lean_object* v_as_586_, size_t v_sz_587_, size_t v_i_588_, lean_object* v_b_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = lean_usize_dec_lt(v_i_588_, v_sz_587_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v_b_589_);
return v___x_594_;
}
else
{
lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_629_; 
v_snd_595_ = lean_ctor_get(v_b_589_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_b_589_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_b_589_, 0);
lean_dec(v_unused_630_);
v___x_597_ = v_b_589_;
v_isShared_598_ = v_isSharedCheck_629_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_dec(v_b_589_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_629_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v_a_600_ = lean_array_uget_borrowed(v_as_586_, v_i_588_);
lean_inc(v_snd_595_);
lean_inc(v_a_600_);
v___x_601_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_a_600_, v_snd_595_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_620_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_620_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_620_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_620_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
if (lean_obj_tag(v_a_602_) == 0)
{
lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_a_602_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_606_);
v___x_608_ = v___x_597_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_snd_595_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_608_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; 
lean_del_object(v___x_604_);
lean_dec(v_snd_595_);
v_a_613_ = lean_ctor_get(v_a_602_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v_a_602_, 1);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v_a_613_);
lean_ctor_set(v___x_597_, 0, v___x_599_);
v___x_615_ = v___x_597_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_a_613_);
v___x_615_ = v_reuseFailAlloc_619_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
size_t v___x_616_; size_t v___x_617_; 
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_588_, v___x_616_);
v_i_588_ = v___x_617_;
v_b_589_ = v___x_615_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
v_a_621_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_601_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_601_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3___boxed(lean_object* v_as_631_, lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_b_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
size_t v_sz_boxed_638_; size_t v_i_boxed_639_; lean_object* v_res_640_; 
v_sz_boxed_638_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_639_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(v_as_631_, v_sz_boxed_638_, v_i_boxed_639_, v_b_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_as_631_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2___boxed(lean_object* v_stx_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_stx_641_, v_b_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(lean_object* v_stx_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(0);
v___x_652_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_stx_647_, v___x_651_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_652_, 0);
lean_dec(v_unused_660_);
v___x_654_ = v___x_652_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___x_652_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_651_);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_651_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_652_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_652_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0___boxed(lean_object* v_stx_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(v_stx_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(lean_object* v_msgData_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v_msgData_709_, v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(v_msgData_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn));
v___x_721_ = l_Lean_Elab_Command_addLinter(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2____boxed(lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_();
return v_res_723_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_GlobalAttributeIn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_GlobalAttributeIn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_GlobalAttributeIn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_GlobalAttributeIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_GlobalAttributeIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_GlobalAttributeIn(builtin);
}
#ifdef __cplusplus
}
#endif
