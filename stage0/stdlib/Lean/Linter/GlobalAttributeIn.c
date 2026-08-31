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
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_249_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_271_; lean_object* v_env_272_; lean_object* v___x_273_; lean_object* v_scopes_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_opts_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_271_ = lean_st_ref_get(v___y_269_);
v_env_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_env_272_);
lean_dec(v___x_271_);
v___x_273_ = lean_st_ref_get(v___y_269_);
v_scopes_274_ = lean_ctor_get(v___x_273_, 2);
lean_inc(v_scopes_274_);
lean_dec(v___x_273_);
v___x_275_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_276_ = l_List_head_x21___redArg(v___x_275_, v_scopes_274_);
lean_dec(v_scopes_274_);
v_opts_277_ = lean_ctor_get(v___x_276_, 1);
lean_inc_ref(v_opts_277_);
lean_dec(v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_279_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___closed__5);
v___x_280_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_280_, 0, v_env_272_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
lean_ctor_set(v___x_280_, 3, v_opts_277_);
v___x_281_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_msgData_268_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v_msgData_283_, v___y_284_);
lean_dec(v___y_284_);
return v_res_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(lean_object* v_opts_287_, lean_object* v_opt_288_){
_start:
{
lean_object* v_name_289_; lean_object* v_defValue_290_; lean_object* v_map_291_; lean_object* v___x_292_; 
v_name_289_ = lean_ctor_get(v_opt_288_, 0);
v_defValue_290_ = lean_ctor_get(v_opt_288_, 1);
v_map_291_ = lean_ctor_get(v_opts_287_, 0);
v___x_292_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_291_, v_name_289_);
if (lean_obj_tag(v___x_292_) == 0)
{
uint8_t v___x_293_; 
v___x_293_ = lean_unbox(v_defValue_290_);
return v___x_293_;
}
else
{
lean_object* v_val_294_; 
v_val_294_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_val_294_);
lean_dec_ref_known(v___x_292_, 1);
if (lean_obj_tag(v_val_294_) == 1)
{
uint8_t v_v_295_; 
v_v_295_ = lean_ctor_get_uint8(v_val_294_, 0);
lean_dec_ref_known(v_val_294_, 0);
return v_v_295_;
}
else
{
uint8_t v___x_296_; 
lean_dec(v_val_294_);
v___x_296_ = lean_unbox(v_defValue_290_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2___boxed(lean_object* v_opts_297_, lean_object* v_opt_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(v_opts_297_, v_opt_298_);
lean_dec_ref(v_opt_298_);
lean_dec_ref(v_opts_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(uint8_t v_suppressElabErrors_302_, uint8_t v___y_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_304_) == 1)
{
lean_object* v_pre_305_; 
v_pre_305_ = lean_ctor_get(v_x_304_, 0);
if (lean_obj_tag(v_pre_305_) == 0)
{
lean_object* v_str_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_str_306_ = lean_ctor_get(v_x_304_, 1);
v___x_307_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___closed__0));
v___x_308_ = lean_string_dec_eq(v_str_306_, v___x_307_);
if (v___x_308_ == 0)
{
return v___x_308_;
}
else
{
return v_suppressElabErrors_302_;
}
}
else
{
return v___y_303_;
}
}
else
{
return v___y_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_309_, lean_object* v___y_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_suppressElabErrors_boxed_312_; uint8_t v___y_4550__boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v_suppressElabErrors_boxed_312_ = lean_unbox(v_suppressElabErrors_309_);
v___y_4550__boxed_313_ = lean_unbox(v___y_310_);
v_res_314_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0(v_suppressElabErrors_boxed_312_, v___y_4550__boxed_313_, v_x_311_);
lean_dec(v_x_311_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(lean_object* v_ref_317_, lean_object* v_msgData_318_, uint8_t v_severity_319_, uint8_t v_isSilent_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___y_325_; lean_object* v___y_326_; uint8_t v___y_327_; lean_object* v___y_328_; lean_object* v___y_329_; lean_object* v___y_330_; uint8_t v___y_331_; lean_object* v___y_332_; uint8_t v___y_390_; lean_object* v___y_391_; uint8_t v___y_392_; uint8_t v___y_393_; lean_object* v___y_394_; uint8_t v___y_418_; uint8_t v___y_419_; lean_object* v___y_420_; uint8_t v___y_421_; lean_object* v___y_422_; uint8_t v___y_426_; uint8_t v___y_427_; uint8_t v___y_428_; uint8_t v___x_443_; uint8_t v___y_445_; uint8_t v___y_446_; uint8_t v___y_447_; uint8_t v___y_449_; uint8_t v___x_461_; 
v___x_443_ = 2;
v___x_461_ = l_Lean_instBEqMessageSeverity_beq(v_severity_319_, v___x_443_);
if (v___x_461_ == 0)
{
v___y_449_ = v___x_461_;
goto v___jp_448_;
}
else
{
uint8_t v___x_462_; 
lean_inc_ref(v_msgData_318_);
v___x_462_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_318_);
v___y_449_ = v___x_462_;
goto v___jp_448_;
}
v___jp_324_:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Elab_Command_getScope___redArg(v___y_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = l_Lean_Elab_Command_getScope___redArg(v___y_332_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_372_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_372_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_372_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_372_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v_currNamespace_341_; lean_object* v_openDecls_342_; lean_object* v_env_343_; lean_object* v_messages_344_; lean_object* v_scopes_345_; lean_object* v_usedQuotCtxts_346_; lean_object* v_nextMacroScope_347_; lean_object* v_maxRecDepth_348_; lean_object* v_ngen_349_; lean_object* v_auxDeclNGen_350_; lean_object* v_infoState_351_; lean_object* v_traceState_352_; lean_object* v_snapshotTasks_353_; lean_object* v_prevLinterStates_354_; lean_object* v_codeQualityEntryTasks_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_371_; 
v___x_340_ = lean_st_ref_take(v___y_332_);
v_currNamespace_341_ = lean_ctor_get(v_a_334_, 2);
lean_inc(v_currNamespace_341_);
lean_dec(v_a_334_);
v_openDecls_342_ = lean_ctor_get(v_a_336_, 3);
lean_inc(v_openDecls_342_);
lean_dec(v_a_336_);
v_env_343_ = lean_ctor_get(v___x_340_, 0);
v_messages_344_ = lean_ctor_get(v___x_340_, 1);
v_scopes_345_ = lean_ctor_get(v___x_340_, 2);
v_usedQuotCtxts_346_ = lean_ctor_get(v___x_340_, 3);
v_nextMacroScope_347_ = lean_ctor_get(v___x_340_, 4);
v_maxRecDepth_348_ = lean_ctor_get(v___x_340_, 5);
v_ngen_349_ = lean_ctor_get(v___x_340_, 6);
v_auxDeclNGen_350_ = lean_ctor_get(v___x_340_, 7);
v_infoState_351_ = lean_ctor_get(v___x_340_, 8);
v_traceState_352_ = lean_ctor_get(v___x_340_, 9);
v_snapshotTasks_353_ = lean_ctor_get(v___x_340_, 10);
v_prevLinterStates_354_ = lean_ctor_get(v___x_340_, 11);
v_codeQualityEntryTasks_355_ = lean_ctor_get(v___x_340_, 12);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_371_ == 0)
{
v___x_357_ = v___x_340_;
v_isShared_358_ = v_isSharedCheck_371_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_codeQualityEntryTasks_355_);
lean_inc(v_prevLinterStates_354_);
lean_inc(v_snapshotTasks_353_);
lean_inc(v_traceState_352_);
lean_inc(v_infoState_351_);
lean_inc(v_auxDeclNGen_350_);
lean_inc(v_ngen_349_);
lean_inc(v_maxRecDepth_348_);
lean_inc(v_nextMacroScope_347_);
lean_inc(v_usedQuotCtxts_346_);
lean_inc(v_scopes_345_);
lean_inc(v_messages_344_);
lean_inc(v_env_343_);
lean_dec(v___x_340_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_371_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_currNamespace_341_);
lean_ctor_set(v___x_359_, 1, v_openDecls_342_);
v___x_360_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
lean_ctor_set(v___x_360_, 1, v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc_ref(v___y_330_);
v___x_361_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_361_, 0, v___y_330_);
lean_ctor_set(v___x_361_, 1, v___y_329_);
lean_ctor_set(v___x_361_, 2, v___y_328_);
lean_ctor_set(v___x_361_, 3, v___y_325_);
lean_ctor_set(v___x_361_, 4, v___x_360_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5, v___y_331_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5 + 1, v___y_327_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*5 + 2, v_isSilent_320_);
v___x_362_ = l_Lean_MessageLog_add(v___x_361_, v_messages_344_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v___x_362_);
v___x_364_ = v___x_357_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_env_343_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_scopes_345_);
lean_ctor_set(v_reuseFailAlloc_370_, 3, v_usedQuotCtxts_346_);
lean_ctor_set(v_reuseFailAlloc_370_, 4, v_nextMacroScope_347_);
lean_ctor_set(v_reuseFailAlloc_370_, 5, v_maxRecDepth_348_);
lean_ctor_set(v_reuseFailAlloc_370_, 6, v_ngen_349_);
lean_ctor_set(v_reuseFailAlloc_370_, 7, v_auxDeclNGen_350_);
lean_ctor_set(v_reuseFailAlloc_370_, 8, v_infoState_351_);
lean_ctor_set(v_reuseFailAlloc_370_, 9, v_traceState_352_);
lean_ctor_set(v_reuseFailAlloc_370_, 10, v_snapshotTasks_353_);
lean_ctor_set(v_reuseFailAlloc_370_, 11, v_prevLinterStates_354_);
lean_ctor_set(v_reuseFailAlloc_370_, 12, v_codeQualityEntryTasks_355_);
v___x_364_ = v_reuseFailAlloc_370_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = lean_st_ref_put(v___y_332_, v___x_364_);
v___x_366_ = lean_box(0);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 0, v___x_366_);
v___x_368_ = v___x_338_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_a_334_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_326_);
v_a_373_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_335_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_335_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_326_);
v_a_381_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_333_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_333_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
v___jp_389_:
{
lean_object* v_fileName_395_; lean_object* v_fileMap_396_; uint8_t v_suppressElabErrors_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_416_; 
v_fileName_395_ = lean_ctor_get(v___y_321_, 0);
v_fileMap_396_ = lean_ctor_get(v___y_321_, 1);
v_suppressElabErrors_397_ = lean_ctor_get_uint8(v___y_321_, sizeof(void*)*10);
v___x_398_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_318_);
v___x_399_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v___x_398_, v___y_322_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_416_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_416_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_416_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc_ref_n(v_fileMap_396_, 2);
v___x_404_ = l_Lean_FileMap_toPosition(v_fileMap_396_, v___y_391_);
lean_dec(v___y_391_);
v___x_405_ = l_Lean_FileMap_toPosition(v_fileMap_396_, v___y_394_);
lean_dec(v___y_394_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___closed__0));
if (v_suppressElabErrors_397_ == 0)
{
lean_del_object(v___x_402_);
v___y_325_ = v___x_407_;
v___y_326_ = v_a_400_;
v___y_327_ = v___y_392_;
v___y_328_ = v___x_406_;
v___y_329_ = v___x_404_;
v___y_330_ = v_fileName_395_;
v___y_331_ = v___y_393_;
v___y_332_ = v___y_322_;
goto v___jp_324_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; uint8_t v___x_411_; 
v___x_408_ = lean_box(v_suppressElabErrors_397_);
v___x_409_ = lean_box(v___y_390_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___lam__0___boxed), 3, 2);
lean_closure_set(v___f_410_, 0, v___x_408_);
lean_closure_set(v___f_410_, 1, v___x_409_);
lean_inc(v_a_400_);
v___x_411_ = l_Lean_MessageData_hasTag(v___f_410_, v_a_400_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_414_; 
lean_dec_ref_known(v___x_406_, 1);
lean_dec_ref(v___x_404_);
lean_dec(v_a_400_);
v___x_412_ = lean_box(0);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_412_);
v___x_414_ = v___x_402_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
else
{
lean_del_object(v___x_402_);
v___y_325_ = v___x_407_;
v___y_326_ = v_a_400_;
v___y_327_ = v___y_392_;
v___y_328_ = v___x_406_;
v___y_329_ = v___x_404_;
v___y_330_ = v_fileName_395_;
v___y_331_ = v___y_393_;
v___y_332_ = v___y_322_;
goto v___jp_324_;
}
}
}
}
v___jp_417_:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Syntax_getTailPos_x3f(v___y_420_, v___y_421_);
lean_dec(v___y_420_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_inc(v___y_422_);
v___y_390_ = v___y_418_;
v___y_391_ = v___y_422_;
v___y_392_ = v___y_419_;
v___y_393_ = v___y_421_;
v___y_394_ = v___y_422_;
goto v___jp_389_;
}
else
{
lean_object* v_val_424_; 
v_val_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v___x_423_, 1);
v___y_390_ = v___y_418_;
v___y_391_ = v___y_422_;
v___y_392_ = v___y_419_;
v___y_393_ = v___y_421_;
v___y_394_ = v_val_424_;
goto v___jp_389_;
}
}
v___jp_425_:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Elab_Command_getRef___redArg(v___y_321_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_ref_431_; lean_object* v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v_ref_431_ = l_Lean_replaceRef(v_ref_317_, v_a_430_);
lean_dec(v_a_430_);
v___x_432_ = l_Lean_Syntax_getPos_x3f(v_ref_431_, v___y_427_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___y_418_ = v___y_426_;
v___y_419_ = v___y_428_;
v___y_420_ = v_ref_431_;
v___y_421_ = v___y_427_;
v___y_422_ = v___x_433_;
goto v___jp_417_;
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_432_, 1);
v___y_418_ = v___y_426_;
v___y_419_ = v___y_428_;
v___y_420_ = v_ref_431_;
v___y_421_ = v___y_427_;
v___y_422_ = v_val_434_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v_msgData_318_);
v_a_435_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_429_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_429_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
v___jp_444_:
{
if (v___y_447_ == 0)
{
v___y_426_ = v___y_445_;
v___y_427_ = v___y_446_;
v___y_428_ = v_severity_319_;
goto v___jp_425_;
}
else
{
v___y_426_ = v___y_445_;
v___y_427_ = v___y_446_;
v___y_428_ = v___x_443_;
goto v___jp_425_;
}
}
v___jp_448_:
{
if (v___y_449_ == 0)
{
lean_object* v___x_450_; lean_object* v_scopes_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_opts_454_; uint8_t v___x_455_; uint8_t v___x_456_; 
v___x_450_ = lean_st_ref_get(v___y_322_);
v_scopes_451_ = lean_ctor_get(v___x_450_, 2);
lean_inc(v_scopes_451_);
lean_dec(v___x_450_);
v___x_452_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_453_ = l_List_head_x21___redArg(v___x_452_, v_scopes_451_);
lean_dec(v_scopes_451_);
v_opts_454_ = lean_ctor_get(v___x_453_, 1);
lean_inc_ref(v_opts_454_);
lean_dec(v___x_453_);
v___x_455_ = 1;
v___x_456_ = l_Lean_instBEqMessageSeverity_beq(v_severity_319_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_opts_454_);
v___y_445_ = v___y_449_;
v___y_446_ = v___y_449_;
v___y_447_ = v___x_456_;
goto v___jp_444_;
}
else
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = l_Lean_warningAsError;
v___x_458_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__2(v_opts_454_, v___x_457_);
lean_dec_ref(v_opts_454_);
v___y_445_ = v___y_449_;
v___y_446_ = v___y_449_;
v___y_447_ = v___x_458_;
goto v___jp_444_;
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec_ref(v_msgData_318_);
v___x_459_ = lean_box(0);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0___boxed(lean_object* v_ref_463_, lean_object* v_msgData_464_, lean_object* v_severity_465_, lean_object* v_isSilent_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
uint8_t v_severity_boxed_470_; uint8_t v_isSilent_boxed_471_; lean_object* v_res_472_; 
v_severity_boxed_470_ = lean_unbox(v_severity_465_);
v_isSilent_boxed_471_ = lean_unbox(v_isSilent_466_);
v_res_472_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(v_ref_463_, v_msgData_464_, v_severity_boxed_470_, v_isSilent_boxed_471_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v_ref_463_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(lean_object* v_ref_473_, lean_object* v_msgData_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = 2;
v___x_479_ = 0;
v___x_480_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0(v_ref_473_, v_msgData_474_, v___x_478_, v___x_479_, v___y_475_, v___y_476_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0___boxed(lean_object* v_ref_481_, lean_object* v_msgData_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(v_ref_481_, v_msgData_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v_ref_481_);
return v_res_486_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__0));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__2));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__4));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__6));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(lean_object* v_fst_499_, lean_object* v_as_500_, size_t v_sz_501_, size_t v_i_502_, lean_object* v_b_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec(v_fst_499_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v_b_503_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_509_ = lean_array_uget_borrowed(v_as_500_, v_i_502_);
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__1);
lean_inc(v_a_509_);
v___x_511_ = l_Lean_MessageData_ofSyntax(v_a_509_);
lean_inc_ref(v___x_511_);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__3);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
lean_inc(v_fst_499_);
v___x_515_ = l_Lean_MessageData_ofSyntax(v_fst_499_);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__5);
v___x_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_511_);
v___x_520_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___closed__7);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0(v_a_509_, v___x_521_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v___x_523_; size_t v___x_524_; size_t v___x_525_; 
lean_dec_ref_known(v___x_522_, 1);
v___x_523_ = lean_box(0);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_i_502_, v___x_524_);
v_i_502_ = v___x_525_;
v_b_503_ = v___x_523_;
goto _start;
}
else
{
lean_dec(v_fst_499_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1___boxed(lean_object* v_fst_527_, lean_object* v_as_528_, lean_object* v_sz_529_, lean_object* v_i_530_, lean_object* v_b_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
size_t v_sz_boxed_535_; size_t v_i_boxed_536_; lean_object* v_res_537_; 
v_sz_boxed_535_ = lean_unbox_usize(v_sz_529_);
lean_dec(v_sz_529_);
v_i_boxed_536_ = lean_unbox_usize(v_i_530_);
lean_dec(v_i_530_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(v_fst_527_, v_as_528_, v_sz_boxed_535_, v_i_boxed_536_, v_b_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v_as_528_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(lean_object* v_stx_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_b_544_; lean_object* v_a_548_; uint8_t v___x_574_; 
v___x_574_ = l_Lean_Syntax_isQuot(v_stx_538_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_box(0);
lean_inc(v_stx_538_);
v___x_576_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_getGlobalAttributesIn_x3f(v_stx_538_);
if (lean_obj_tag(v___x_576_) == 1)
{
lean_object* v_val_577_; lean_object* v_fst_578_; lean_object* v_snd_579_; size_t v_sz_580_; size_t v___x_581_; lean_object* v___x_582_; 
v_val_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v___x_576_, 1);
v_fst_578_ = lean_ctor_get(v_val_577_, 0);
lean_inc(v_fst_578_);
v_snd_579_ = lean_ctor_get(v_val_577_, 1);
lean_inc(v_snd_579_);
lean_dec(v_val_577_);
v_sz_580_ = lean_array_size(v_snd_579_);
v___x_581_ = ((size_t)0ULL);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__1(v_fst_578_, v_snd_579_, v_sz_580_, v___x_581_, v___x_575_, v___y_540_, v___y_541_);
lean_dec(v_snd_579_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_dec_ref_known(v___x_582_, 1);
v_a_548_ = v___x_575_;
goto v___jp_547_;
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec(v_stx_538_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_dec(v___x_576_);
v_a_548_ = v___x_575_;
goto v___jp_547_;
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_stx_538_);
v___x_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_591_, 0, v_b_539_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_b_544_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
v___jp_547_:
{
if (lean_obj_tag(v_stx_538_) == 1)
{
lean_object* v_args_549_; lean_object* v___x_550_; lean_object* v___x_551_; size_t v_sz_552_; size_t v___x_553_; lean_object* v___x_554_; 
v_args_549_ = lean_ctor_get(v_stx_538_, 2);
lean_inc_ref(v_args_549_);
lean_dec_ref_known(v_stx_538_, 3);
v___x_550_ = lean_box(0);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_a_548_);
v_sz_552_ = lean_array_size(v_args_549_);
v___x_553_ = ((size_t)0ULL);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(v_args_549_, v_sz_552_, v___x_553_, v___x_551_, v___y_540_, v___y_541_);
lean_dec_ref(v_args_549_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_565_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_565_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_565_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_fst_559_; 
v_fst_559_ = lean_ctor_get(v_a_555_, 0);
if (lean_obj_tag(v_fst_559_) == 0)
{
lean_object* v_snd_560_; 
lean_del_object(v___x_557_);
v_snd_560_ = lean_ctor_get(v_a_555_, 1);
lean_inc(v_snd_560_);
lean_dec(v_a_555_);
v_b_544_ = v_snd_560_;
goto v___jp_543_;
}
else
{
lean_object* v_val_561_; lean_object* v___x_563_; 
lean_inc_ref(v_fst_559_);
lean_dec(v_a_555_);
v_val_561_ = lean_ctor_get(v_fst_559_, 0);
lean_inc(v_val_561_);
lean_dec_ref_known(v_fst_559_, 1);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v_val_561_);
v___x_563_ = v___x_557_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_val_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
v_a_566_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_554_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_554_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_dec(v_stx_538_);
v_b_544_ = v_a_548_;
goto v___jp_543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(lean_object* v_as_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_b_596_);
return v___x_601_;
}
else
{
lean_object* v_snd_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_636_; 
v_snd_602_ = lean_ctor_get(v_b_596_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_b_596_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v_b_596_, 0);
lean_dec(v_unused_637_);
v___x_604_ = v_b_596_;
v_isShared_605_ = v_isSharedCheck_636_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snd_602_);
lean_dec(v_b_596_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_636_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_a_606_; lean_object* v___x_607_; 
v_a_606_ = lean_array_uget_borrowed(v_as_593_, v_i_595_);
lean_inc(v_snd_602_);
lean_inc(v_a_606_);
v___x_607_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_a_606_, v_snd_602_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_627_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
if (lean_obj_tag(v_a_608_) == 0)
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v_a_608_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_612_);
v___x_614_ = v___x_604_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_snd_602_);
v___x_614_ = v_reuseFailAlloc_618_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_614_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
lean_del_object(v___x_610_);
lean_dec(v_snd_602_);
v_a_619_ = lean_ctor_get(v_a_608_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v_a_608_, 1);
v___x_620_ = lean_box(0);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_a_619_);
lean_ctor_set(v___x_604_, 0, v___x_620_);
v___x_622_ = v___x_604_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_a_619_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
size_t v___x_623_; size_t v___x_624_; 
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_595_, v___x_623_);
v_i_595_ = v___x_624_;
v_b_596_ = v___x_622_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_del_object(v___x_604_);
lean_dec(v_snd_602_);
v_a_628_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_607_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_607_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3___boxed(lean_object* v_as_638_, lean_object* v_sz_639_, lean_object* v_i_640_, lean_object* v_b_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
size_t v_sz_boxed_645_; size_t v_i_boxed_646_; lean_object* v_res_647_; 
v_sz_boxed_645_ = lean_unbox_usize(v_sz_639_);
lean_dec(v_sz_639_);
v_i_boxed_646_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_res_647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2_spec__3(v_as_638_, v_sz_boxed_645_, v_i_boxed_646_, v_b_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_as_638_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2___boxed(lean_object* v_stx_648_, lean_object* v_b_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_stx_648_, v_b_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(lean_object* v_stx_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_box(0);
v___x_659_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_instForInTopDownSkipQuotSyntaxOfMonad_loop___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__2(v_stx_654_, v___x_658_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_659_, 0);
lean_dec(v_unused_667_);
v___x_661_ = v___x_659_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_dec(v___x_659_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_658_);
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_658_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_a_668_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_659_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_659_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0___boxed(lean_object* v_stx_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn___lam__0(v_stx_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(lean_object* v_msgData_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___redArg(v_msgData_716_, v___y_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00__private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn_spec__0_spec__0_spec__1(v_msgData_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_globalAttributeIn));
v___x_728_ = l_Lean_Elab_Command_addLinter(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2____boxed(lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Lean_Linter_GlobalAttributeIn_0__Lean_Linter_initFn_00___x40_Lean_Linter_GlobalAttributeIn_801426259____hygCtx___hyg_2_();
return v_res_730_;
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
