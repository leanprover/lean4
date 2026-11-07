// Lean compiler output
// Module: Lake.Toml.Elab.Expression
// Imports: public import Lake.Toml.Elab.Value meta import all Lake.Toml.Grammar
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_findIdx_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___redArg();
size_t lean_usize_of_nat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_Toml_RBDict_appendArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_elabSimpleKey(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Toml_elabVal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instInhabitedKeyTy_default;
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "table"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "array"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "dotted"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instToStringKeyTy___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object*);
static const lean_array_object l_Lake_Toml_instInhabitedElabState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_instInhabitedElabState_default___closed__0 = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__0_value;
static const lean_ctor_object l_Lake_Toml_instInhabitedElabState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__0_value)}};
static const lean_object* l_Lake_Toml_instInhabitedElabState_default___closed__1 = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instInhabitedElabState_default = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedElabState = (const lean_object*)&l_Lake_Toml_instInhabitedElabState_default___closed__1_value;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cannot redefine "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpleKey"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(187, 51, 117, 190, 121, 223, 170, 220)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "keyval"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 46, 78, 232, 161, 211, 209, 25)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ill-formed key-value pair syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed key syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7;
static const lean_array_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "(internal) bad array key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdTable"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 45, 156, 80, 41, 178, 181, 196)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrayTable"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 220, 56, 86, 146, 203, 81, 19)}};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "ill-formed array table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed expression syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0 = (const lean_object*)&l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabToml___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l_Lake_Toml_elabToml___closed__0 = (const lean_object*)&l_Lake_Toml_elabToml___closed__0_value;
static const lean_ctor_object l_Lake_Toml_elabToml___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_elabToml___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 110, 132, 157, 201, 185, 149, 61)}};
static const lean_object* l_Lake_Toml_elabToml___closed__1 = (const lean_object*)&l_Lake_Toml_elabToml___closed__1_value;
static const lean_string_object l_Lake_Toml_elabToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ill-formed TOML syntax"};
static const lean_object* l_Lake_Toml_elabToml___closed__2 = (const lean_object*)&l_Lake_Toml_elabToml___closed__2_value;
static lean_once_cell_t l_Lake_Toml_elabToml___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabToml___closed__3;
static const lean_ctor_object l_Lake_Toml_elabToml___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabToml___closed__4_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4_value),LEAN_SCALAR_PTR_LITERAL(169, 19, 11, 35, 86, 242, 57, 11)}};
static const lean_object* l_Lake_Toml_elabToml___closed__4 = (const lean_object*)&l_Lake_Toml_elabToml___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(lean_object* v_value_22_){
_start:
{
lean_inc(v_value_22_);
return v_value_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg___boxed(lean_object* v_value_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___redArg(v_value_23_);
lean_dec(v_value_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_value_28_){
_start:
{
lean_inc(v_value_28_);
return v_value_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_value_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_value_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_value_32_);
lean_dec(v_value_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(lean_object* v_stdTable_35_){
_start:
{
lean_inc(v_stdTable_35_);
return v_stdTable_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg___boxed(lean_object* v_stdTable_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___redArg(v_stdTable_36_);
lean_dec(v_stdTable_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_stdTable_41_){
_start:
{
lean_inc(v_stdTable_41_);
return v_stdTable_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_stdTable_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_stdTable_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_stdTable_45_);
lean_dec(v_stdTable_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(lean_object* v_array_48_){
_start:
{
lean_inc(v_array_48_);
return v_array_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg___boxed(lean_object* v_array_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___redArg(v_array_49_);
lean_dec(v_array_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_array_54_){
_start:
{
lean_inc(v_array_54_);
return v_array_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_array_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_array_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_array_58_);
lean_dec(v_array_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(lean_object* v_dottedPrefix_61_){
_start:
{
lean_inc(v_dottedPrefix_61_);
return v_dottedPrefix_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg___boxed(lean_object* v_dottedPrefix_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___redArg(v_dottedPrefix_62_);
lean_dec(v_dottedPrefix_62_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(lean_object* v_motive_64_, uint8_t v_t_65_, lean_object* v_h_66_, lean_object* v_dottedPrefix_67_){
_start:
{
lean_inc(v_dottedPrefix_67_);
return v_dottedPrefix_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_dottedPrefix_71_){
_start:
{
uint8_t v_t_boxed_72_; lean_object* v_res_73_; 
v_t_boxed_72_ = lean_unbox(v_t_69_);
v_res_73_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_dottedPrefix_elim(v_motive_68_, v_t_boxed_72_, v_h_70_, v_dottedPrefix_71_);
lean_dec(v_dottedPrefix_71_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(lean_object* v_headerPrefix_74_){
_start:
{
lean_inc(v_headerPrefix_74_);
return v_headerPrefix_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg___boxed(lean_object* v_headerPrefix_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___redArg(v_headerPrefix_75_);
lean_dec(v_headerPrefix_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(lean_object* v_motive_77_, uint8_t v_t_78_, lean_object* v_h_79_, lean_object* v_headerPrefix_80_){
_start:
{
lean_inc(v_headerPrefix_80_);
return v_headerPrefix_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim___boxed(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_headerPrefix_84_){
_start:
{
uint8_t v_t_boxed_85_; lean_object* v_res_86_; 
v_t_boxed_85_ = lean_unbox(v_t_82_);
v_res_86_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_headerPrefix_elim(v_motive_81_, v_t_boxed_85_, v_h_83_, v_headerPrefix_84_);
lean_dec(v_headerPrefix_84_);
return v_res_86_;
}
}
static uint8_t _init_l_Lake_Toml_instInhabitedKeyTy_default(void){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
static uint8_t _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy(void){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(uint8_t v_ty_94_){
_start:
{
switch(v_ty_94_)
{
case 0:
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__0));
return v___x_95_;
}
case 1:
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__1));
return v___x_96_;
}
case 2:
{
lean_object* v___x_97_; 
v___x_97_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__2));
return v___x_97_;
}
case 3:
{
lean_object* v___x_98_; 
v___x_98_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__3));
return v___x_98_;
}
default: 
{
lean_object* v___x_99_; 
v___x_99_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___closed__4));
return v___x_99_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString___boxed(lean_object* v_ty_100_){
_start:
{
uint8_t v_ty_boxed_101_; lean_object* v_res_102_; 
v_ty_boxed_101_ = lean_unbox(v_ty_100_);
v_res_102_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v_ty_boxed_101_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(uint8_t v_ty_105_){
_start:
{
switch(v_ty_105_)
{
case 1:
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
case 4:
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
case 3:
{
uint8_t v___x_108_; 
v___x_108_ = 1;
return v___x_108_;
}
default: 
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix___boxed(lean_object* v_ty_110_){
_start:
{
uint8_t v_ty_boxed_111_; uint8_t v_res_112_; lean_object* v_r_113_; 
v_ty_boxed_111_ = lean_unbox(v_ty_110_);
v_res_112_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_isValidPrefix(v_ty_boxed_111_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_122_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__0);
v___x_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
lean_ctor_set(v___x_127_, 4, v___x_125_);
lean_ctor_set(v___x_127_, 5, v___x_125_);
lean_ctor_set(v___x_127_, 6, v___x_125_);
lean_ctor_set(v___x_127_, 7, v___x_125_);
lean_ctor_set(v___x_127_, 8, v___x_125_);
lean_ctor_set(v___x_127_, 9, v___x_125_);
lean_ctor_set(v___x_127_, 10, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(32u);
v___x_129_ = lean_mk_empty_array_with_capacity(v___x_128_);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_131_ = ((size_t)5ULL);
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_unsigned_to_nat(32u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__3);
v___x_136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_132_);
lean_ctor_set(v___x_136_, 3, v___x_132_);
lean_ctor_set_usize(v___x_136_, 4, v___x_131_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_box(1);
v___x_138_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__4);
v___x_139_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__1);
v___x_140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(lean_object* v_msgData_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; lean_object* v_toCold_146_; lean_object* v_env_147_; lean_object* v_options_148_; uint8_t v___x_149_; lean_object* v_env_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_145_ = lean_st_ref_get(v___y_143_);
v_toCold_146_ = lean_ctor_get(v___y_142_, 0);
v_env_147_ = lean_ctor_get(v___x_145_, 0);
lean_inc_ref(v_env_147_);
lean_dec(v___x_145_);
v_options_148_ = lean_ctor_get(v_toCold_146_, 2);
v___x_149_ = 0;
v_env_150_ = l_Lean_Environment_setRecordingDeps(v_env_147_, v___x_149_);
v___x_151_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__2);
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_148_);
v___x_153_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_153_, 0, v_env_150_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
lean_ctor_set(v___x_153_, 3, v_options_148_);
v___x_154_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_msgData_141_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msgData_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(lean_object* v_msg_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_ref_165_; lean_object* v___x_166_; lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_175_; 
v_ref_165_ = lean_ctor_get(v___y_162_, 2);
v___x_166_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_161_, v___y_162_, v___y_163_);
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_175_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_175_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_173_; 
lean_inc(v_ref_165_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_ref_165_);
lean_ctor_set(v___x_171_, 1, v_a_167_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 1);
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_173_ = v___x_169_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg___boxed(lean_object* v_msg_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(lean_object* v_ref_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_toCold_187_; lean_object* v_currRecDepth_188_; lean_object* v_ref_189_; uint16_t v_optionFlags_190_; uint8_t v_suppressElabErrors_191_; uint8_t v_checkDeprecated_192_; uint8_t v_isRecordingDeps_193_; lean_object* v_ref_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_toCold_187_ = lean_ctor_get(v___y_184_, 0);
v_currRecDepth_188_ = lean_ctor_get(v___y_184_, 1);
v_ref_189_ = lean_ctor_get(v___y_184_, 2);
v_optionFlags_190_ = lean_ctor_get_uint16(v___y_184_, sizeof(void*)*3);
v_suppressElabErrors_191_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*3 + 2);
v_checkDeprecated_192_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*3 + 3);
v_isRecordingDeps_193_ = lean_ctor_get_uint8(v___y_184_, sizeof(void*)*3 + 4);
v_ref_194_ = l_Lean_replaceRef(v_ref_181_, v_ref_189_);
lean_inc(v_currRecDepth_188_);
lean_inc_ref(v_toCold_187_);
v___x_195_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_195_, 0, v_toCold_187_);
lean_ctor_set(v___x_195_, 1, v_currRecDepth_188_);
lean_ctor_set(v___x_195_, 2, v_ref_194_);
lean_ctor_set_uint16(v___x_195_, sizeof(void*)*3, v_optionFlags_190_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 2, v_suppressElabErrors_191_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 3, v_checkDeprecated_192_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*3 + 4, v_isRecordingDeps_193_);
v___x_196_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_182_, v___x_195_, v___y_185_);
lean_dec_ref_known(v___x_195_, 3);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg___boxed(lean_object* v_ref_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_197_, v_msg_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v_ref_197_);
return v_res_203_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_206_ = l_Lean_stringToMessageData(v___x_205_);
return v___x_206_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_209_ = l_Lean_stringToMessageData(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(lean_object* v_as_213_, size_t v_i_214_, size_t v_stop_215_, lean_object* v_b_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; uint8_t v___x_227_; 
v___x_227_ = lean_usize_dec_eq(v_i_214_, v_stop_215_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_array_uget_borrowed(v_as_213_, v_i_214_);
lean_inc(v___x_228_);
v___x_229_ = l_Lake_Toml_elabSimpleKey(v___x_228_, v___y_218_, v___y_219_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v_keyTys_231_; lean_object* v_arrKeyTys_232_; lean_object* v_arrParents_233_; lean_object* v_currArrKey_234_; lean_object* v_currKey_235_; lean_object* v_items_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v_keyTys_231_ = lean_ctor_get(v___y_217_, 0);
v_arrKeyTys_232_ = lean_ctor_get(v___y_217_, 1);
v_arrParents_233_ = lean_ctor_get(v___y_217_, 2);
v_currArrKey_234_ = lean_ctor_get(v___y_217_, 3);
v_currKey_235_ = lean_ctor_get(v___y_217_, 4);
v_items_236_ = lean_ctor_get(v___y_217_, 5);
v___x_237_ = l_Lean_Name_str___override(v_b_216_, v_a_230_);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_231_, v___x_237_);
if (lean_obj_tag(v___x_238_) == 1)
{
lean_object* v_val_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_269_; 
v_val_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_269_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_269_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_val_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_269_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_val_239_);
if (v___x_243_ == 3)
{
lean_del_object(v___x_241_);
lean_dec(v_val_239_);
v_fst_222_ = v___x_237_;
v_snd_223_ = v___y_217_;
goto v___jp_221_;
}
else
{
lean_object* v___x_244_; uint8_t v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_245_ = lean_unbox(v_val_239_);
lean_dec(v_val_239_);
v___x_246_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_245_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 3);
lean_ctor_set(v___x_241_, 0, v___x_246_);
v___x_248_ = v___x_241_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_268_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_249_ = l_Lean_MessageData_ofFormat(v___x_248_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_244_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc(v___x_237_);
v___x_253_ = l_Lean_MessageData_ofName(v___x_237_);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_228_, v___x_256_, v___y_217_, v___y_218_, v___y_219_);
lean_dec_ref(v___y_217_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v_snd_259_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_a_258_);
lean_dec_ref_known(v___x_257_, 1);
v_snd_259_ = lean_ctor_get(v_a_258_, 1);
lean_inc(v_snd_259_);
lean_dec(v_a_258_);
v_fst_222_ = v___x_237_;
v_snd_223_ = v_snd_259_;
goto v___jp_221_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v___x_237_);
v_a_260_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_257_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_257_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_279_; 
lean_inc_ref(v_items_236_);
lean_inc(v_currKey_235_);
lean_inc(v_currArrKey_234_);
lean_inc(v_arrParents_233_);
lean_inc(v_arrKeyTys_232_);
lean_inc(v_keyTys_231_);
lean_dec(v___x_238_);
v_isSharedCheck_279_ = !lean_is_exclusive(v___y_217_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; 
v_unused_280_ = lean_ctor_get(v___y_217_, 5);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v___y_217_, 4);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v___y_217_, 3);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v___y_217_, 2);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v___y_217_, 1);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v___y_217_, 0);
lean_dec(v_unused_285_);
v___x_271_ = v___y_217_;
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___y_217_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_279_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_273_ = 3;
v___x_274_ = lean_box(v___x_273_);
lean_inc(v___x_237_);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_237_, v___x_274_, v_keyTys_231_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_277_ = v___x_271_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_arrKeyTys_232_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_arrParents_233_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_currArrKey_234_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_currKey_235_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_items_236_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
v_fst_222_ = v___x_237_;
v_snd_223_ = v___x_277_;
goto v___jp_221_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v___y_217_);
lean_dec(v_b_216_);
v_a_286_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_229_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_229_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_b_216_);
lean_ctor_set(v___x_294_, 1, v___y_217_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
v___jp_221_:
{
size_t v___x_224_; size_t v___x_225_; 
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_i_214_, v___x_224_);
v_i_214_ = v___x_225_;
v_b_216_ = v_fst_222_;
v___y_217_ = v_snd_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___boxed(lean_object* v_as_296_, lean_object* v_i_297_, lean_object* v_stop_298_, lean_object* v_b_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
size_t v_i_boxed_304_; size_t v_stop_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_304_ = lean_unbox_usize(v_i_297_);
lean_dec(v_i_297_);
v_stop_boxed_305_ = lean_unbox_usize(v_stop_298_);
lean_dec(v_stop_298_);
v_res_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_as_296_, v_i_boxed_304_, v_stop_boxed_305_, v_b_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v_as_296_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(lean_object* v_ks_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_currKey_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_currKey_312_ = lean_ctor_get(v_a_308_, 4);
lean_inc(v_currKey_312_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_array_get_size(v_ks_307_);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v_currKey_312_);
lean_ctor_set(v___x_316_, 1, v_a_308_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_314_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1(v_ks_307_, v___x_318_, v___x_319_, v_currKey_312_, v_a_308_, v_a_309_, v_a_310_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys___boxed(lean_object* v_ks_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v_ks_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec_ref(v_ks_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(lean_object* v_00_u03b1_327_, lean_object* v_ref_328_, lean_object* v_msg_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_ref_328_, v_msg_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___boxed(lean_object* v_00_u03b1_335_, lean_object* v_ref_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0(v_00_u03b1_335_, v_ref_336_, v_msg_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v_ref_336_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(lean_object* v_00_u03b1_343_, lean_object* v_msg_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v_msg_344_, v___y_346_, v___y_347_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___boxed(lean_object* v_00_u03b1_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0(v_00_u03b1_350_, v_msg_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v___y_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(uint8_t v___x_357_, lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___y_363_; uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_367_ == 0)
{
lean_object* v_fst_368_; uint8_t v___x_369_; 
v_fst_368_ = lean_ctor_get(v_b_361_, 0);
v___x_369_ = lean_unbox(v_fst_368_);
if (v___x_369_ == 0)
{
lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_snd_370_ = lean_ctor_get(v_b_361_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_b_361_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v_b_361_, 0);
lean_dec(v_unused_379_);
v___x_372_ = v_b_361_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_dec(v_b_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(v___x_357_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_snd_370_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v___y_363_ = v___x_376_;
goto v___jp_362_;
}
}
}
else
{
lean_object* v_snd_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_390_; 
v_snd_380_ = lean_ctor_get(v_b_361_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_b_361_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_b_361_, 0);
lean_dec(v_unused_391_);
v___x_382_ = v_b_361_;
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_snd_380_);
lean_dec(v_b_361_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_390_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_384_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
lean_inc(v___x_384_);
v___x_385_ = lean_array_push(v_snd_380_, v___x_384_);
v___x_386_ = lean_box(v___x_367_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_385_);
lean_ctor_set(v___x_382_, 0, v___x_386_);
v___x_388_ = v___x_382_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_385_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v___y_363_ = v___x_388_;
goto v___jp_362_;
}
}
}
}
else
{
return v_b_361_;
}
v___jp_362_:
{
size_t v___x_364_; size_t v___x_365_; 
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_359_, v___x_364_);
v_i_359_ = v___x_365_;
v_b_361_ = v___y_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1___boxed(lean_object* v___x_392_, lean_object* v_as_393_, lean_object* v_i_394_, lean_object* v_stop_395_, lean_object* v_b_396_){
_start:
{
uint8_t v___x_2936__boxed_397_; size_t v_i_boxed_398_; size_t v_stop_boxed_399_; lean_object* v_res_400_; 
v___x_2936__boxed_397_ = lean_unbox(v___x_392_);
v_i_boxed_398_ = lean_unbox_usize(v_i_394_);
lean_dec(v_i_394_);
v_stop_boxed_399_ = lean_unbox_usize(v_stop_395_);
lean_dec(v_stop_395_);
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_2936__boxed_397_, v_as_393_, v_i_boxed_398_, v_stop_boxed_399_, v_b_396_);
lean_dec_ref(v_as_393_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(size_t v_sz_408_, size_t v_i_409_, lean_object* v_bs_410_){
_start:
{
uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_lt(v_i_409_, v_sz_408_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_bs_410_);
return v___x_412_;
}
else
{
lean_object* v_v_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_v_413_ = lean_array_uget(v_bs_410_, v_i_409_);
v___x_414_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___closed__3));
lean_inc(v_v_413_);
v___x_415_ = l_Lean_Syntax_isOfKind(v_v_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_dec(v_v_413_);
lean_dec_ref(v_bs_410_);
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v_bs_x27_418_; size_t v___x_419_; size_t v___x_420_; lean_object* v___x_421_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v_bs_x27_418_ = lean_array_uset(v_bs_410_, v_i_409_, v___x_417_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_409_, v___x_419_);
v___x_421_ = lean_array_uset(v_bs_x27_418_, v_i_409_, v_v_413_);
v_i_409_ = v___x_420_;
v_bs_410_ = v___x_421_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0___boxed(lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_bs_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_boxed_426_, v_i_boxed_427_, v_bs_425_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__2));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__6));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(lean_object* v_kv_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_kv_447_);
v___x_453_ = l_Lean_Syntax_isOfKind(v_kv_447_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__3);
v___x_455_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_kv_447_, v___x_454_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_448_);
lean_dec(v_kv_447_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = l_Lean_Syntax_getArg(v_kv_447_, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_457_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_kv_447_);
v___x_460_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_461_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_457_, v___x_460_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_448_);
lean_dec(v___x_457_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v_v_463_; lean_object* v___y_465_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_462_ = lean_unsigned_to_nat(2u);
v_v_463_ = l_Lean_Syntax_getArg(v_kv_447_, v___x_462_);
lean_dec(v_kv_447_);
v___x_571_ = l_Lean_Syntax_getArg(v___x_457_, v___x_456_);
v___x_572_ = l_Lean_Syntax_getArgs(v___x_571_);
lean_dec(v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_574_ = lean_array_get_size(v___x_572_);
v___x_575_ = lean_nat_dec_lt(v___x_456_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec_ref(v___x_572_);
v___y_465_ = v___x_573_;
goto v___jp_464_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; lean_object* v_snd_581_; 
v___x_576_ = lean_box(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_573_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_574_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_459_, v___x_572_, v___x_578_, v___x_579_, v___x_577_);
lean_dec_ref(v___x_572_);
v_snd_581_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_snd_581_);
lean_dec_ref(v___x_580_);
v___y_465_ = v_snd_581_;
goto v___jp_464_;
}
v___jp_464_:
{
size_t v_sz_466_; size_t v___x_467_; lean_object* v___x_468_; 
v_sz_466_ = lean_array_size(v___y_465_);
v___x_467_ = ((size_t)0ULL);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_466_, v___x_467_, v___y_465_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_v_463_);
v___x_469_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_470_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_457_, v___x_469_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v_a_448_);
lean_dec(v___x_457_);
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_tailKeyStx_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_val_471_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_468_, 1);
v___x_472_ = lean_box(0);
v___x_473_ = lean_array_get_size(v_val_471_);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_sub(v___x_473_, v___x_474_);
v_tailKeyStx_476_ = lean_array_get(v___x_472_, v_val_471_, v___x_475_);
lean_dec(v___x_475_);
v___x_477_ = lean_array_pop(v_val_471_);
v___x_478_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys(v___x_477_, v_a_448_, v_a_449_, v_a_450_);
lean_dec_ref(v___x_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v_fst_480_; lean_object* v_snd_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_562_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_fst_480_ = lean_ctor_get(v_a_479_, 0);
v_snd_481_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_562_ == 0)
{
v___x_483_ = v_a_479_;
v_isShared_484_ = v_isSharedCheck_562_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_snd_481_);
lean_inc(v_fst_480_);
lean_dec(v_a_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_562_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; 
lean_inc(v_tailKeyStx_476_);
v___x_485_ = l_Lake_Toml_elabSimpleKey(v_tailKeyStx_476_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v_keyTys_487_; lean_object* v_arrKeyTys_488_; lean_object* v_arrParents_489_; lean_object* v_currArrKey_490_; lean_object* v_currKey_491_; lean_object* v_items_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_485_, 1);
v_keyTys_487_ = lean_ctor_get(v_snd_481_, 0);
v_arrKeyTys_488_ = lean_ctor_get(v_snd_481_, 1);
v_arrParents_489_ = lean_ctor_get(v_snd_481_, 2);
v_currArrKey_490_ = lean_ctor_get(v_snd_481_, 3);
v_currKey_491_ = lean_ctor_get(v_snd_481_, 4);
v_items_492_ = lean_ctor_get(v_snd_481_, 5);
v___x_493_ = l_Lean_Name_str___override(v_fst_480_, v_a_486_);
v___x_494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_487_, v___x_493_);
if (lean_obj_tag(v___x_494_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_514_; 
lean_del_object(v___x_483_);
lean_dec(v_v_463_);
lean_dec(v___x_457_);
v_val_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_499_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_500_ = lean_unbox(v_val_495_);
lean_dec(v_val_495_);
v___x_501_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_500_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 3);
lean_ctor_set(v___x_497_, 0, v___x_501_);
v___x_503_ = v___x_497_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_513_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_504_ = l_Lean_MessageData_ofFormat(v___x_503_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_499_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = l_Lean_MessageData_ofName(v___x_493_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKeyStx_476_, v___x_511_, v_snd_481_, v_a_449_, v_a_450_);
lean_dec(v_snd_481_);
lean_dec(v_tailKeyStx_476_);
return v___x_512_;
}
}
}
else
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_items_492_);
lean_inc(v_currKey_491_);
lean_inc(v_currArrKey_490_);
lean_inc(v_arrParents_489_);
lean_inc(v_arrKeyTys_488_);
lean_inc(v_keyTys_487_);
lean_dec(v___x_494_);
lean_dec(v_tailKeyStx_476_);
v_isSharedCheck_547_ = !lean_is_exclusive(v_snd_481_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; lean_object* v_unused_550_; lean_object* v_unused_551_; lean_object* v_unused_552_; lean_object* v_unused_553_; 
v_unused_548_ = lean_ctor_get(v_snd_481_, 5);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_snd_481_, 4);
lean_dec(v_unused_549_);
v_unused_550_ = lean_ctor_get(v_snd_481_, 3);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_snd_481_, 2);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_snd_481_, 1);
lean_dec(v_unused_552_);
v_unused_553_ = lean_ctor_get(v_snd_481_, 0);
lean_dec(v_unused_553_);
v___x_516_ = v_snd_481_;
v_isShared_517_ = v_isSharedCheck_547_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_snd_481_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_547_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lake_Toml_elabVal(v_v_463_, v_a_449_, v_a_450_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_538_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_538_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_538_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_523_ = lean_box(0);
v___x_524_ = 0;
v___x_525_ = lean_box(v___x_524_);
lean_inc(v___x_493_);
v___x_526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_493_, v___x_525_, v_keyTys_487_);
v___x_527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_527_, 0, v___x_457_);
lean_ctor_set(v___x_527_, 1, v___x_493_);
lean_ctor_set(v___x_527_, 2, v_a_519_);
v___x_528_ = lean_array_push(v_items_492_, v___x_527_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 5, v___x_528_);
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_530_ = v___x_516_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v_arrKeyTys_488_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_arrParents_489_);
lean_ctor_set(v_reuseFailAlloc_537_, 3, v_currArrKey_490_);
lean_ctor_set(v_reuseFailAlloc_537_, 4, v_currKey_491_);
lean_ctor_set(v_reuseFailAlloc_537_, 5, v___x_528_);
v___x_530_ = v_reuseFailAlloc_537_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_530_);
lean_ctor_set(v___x_483_, 0, v___x_523_);
v___x_532_ = v___x_483_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_530_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_534_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_532_);
v___x_534_ = v___x_521_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_del_object(v___x_516_);
lean_dec(v___x_493_);
lean_dec_ref(v_items_492_);
lean_dec(v_currKey_491_);
lean_dec(v_currArrKey_490_);
lean_dec(v_arrParents_489_);
lean_dec(v_arrKeyTys_488_);
lean_dec(v_keyTys_487_);
lean_del_object(v___x_483_);
lean_dec(v___x_457_);
v_a_539_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_518_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_518_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_483_);
lean_dec(v_snd_481_);
lean_dec(v_fst_480_);
lean_dec(v_tailKeyStx_476_);
lean_dec(v_v_463_);
lean_dec(v___x_457_);
v_a_554_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_485_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_485_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_tailKeyStx_476_);
lean_dec(v_v_463_);
lean_dec(v___x_457_);
v_a_563_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_478_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_478_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
if (v_isShared_566_ == 0)
{
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_a_563_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___boxed(lean_object* v_kv_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_kv_582_, v_a_583_, v_a_584_, v_a_585_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_587_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__0));
v___x_590_ = l_Lean_stringToMessageData(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(lean_object* v_as_591_, size_t v_i_592_, size_t v_stop_593_, lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_fst_600_; lean_object* v_snd_601_; uint8_t v___x_605_; 
v___x_605_ = lean_usize_dec_eq(v_i_592_, v_stop_593_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_array_uget_borrowed(v_as_591_, v_i_592_);
lean_inc(v___x_606_);
v___x_607_ = l_Lake_Toml_elabSimpleKey(v___x_606_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v_keyTys_609_; lean_object* v_arrKeyTys_610_; lean_object* v_arrParents_611_; lean_object* v_currArrKey_612_; lean_object* v_currKey_613_; lean_object* v_items_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v_keyTys_609_ = lean_ctor_get(v___y_595_, 0);
v_arrKeyTys_610_ = lean_ctor_get(v___y_595_, 1);
v_arrParents_611_ = lean_ctor_get(v___y_595_, 2);
v_currArrKey_612_ = lean_ctor_get(v___y_595_, 3);
v_currKey_613_ = lean_ctor_get(v___y_595_, 4);
v_items_614_ = lean_ctor_get(v___y_595_, 5);
v___x_615_ = l_Lean_Name_str___override(v_b_594_, v_a_608_);
v___x_616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_609_, v___x_615_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_678_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_678_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_678_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_678_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___x_621_; 
v___x_621_ = lean_unbox(v_val_617_);
switch(v___x_621_)
{
case 2:
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_646_; 
lean_inc_ref(v_items_614_);
lean_inc(v_currKey_613_);
lean_inc(v_arrParents_611_);
lean_inc(v_arrKeyTys_610_);
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_isSharedCheck_646_ = !lean_is_exclusive(v___y_595_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; lean_object* v_unused_648_; lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_647_ = lean_ctor_get(v___y_595_, 5);
lean_dec(v_unused_647_);
v_unused_648_ = lean_ctor_get(v___y_595_, 4);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v___y_595_, 3);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v___y_595_, 2);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v___y_595_, 1);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v___y_595_, 0);
lean_dec(v_unused_652_);
v___x_623_ = v___y_595_;
v_isShared_624_ = v_isSharedCheck_646_;
goto v_resetjp_622_;
}
else
{
lean_dec(v___y_595_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_646_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; 
v___x_625_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_610_, v___x_615_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; lean_object* v___x_628_; 
v_val_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v___x_625_, 1);
lean_inc(v___x_615_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 3, v___x_615_);
lean_ctor_set(v___x_623_, 0, v_val_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_val_626_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_arrKeyTys_610_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_arrParents_611_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_currKey_613_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_items_614_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_fst_600_ = v___x_615_;
v_snd_601_ = v___x_628_;
goto v___jp_599_;
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec(v___x_625_);
lean_del_object(v___x_623_);
lean_dec_ref(v_items_614_);
lean_dec(v_currKey_613_);
lean_dec(v_arrParents_611_);
lean_dec(v_arrKeyTys_610_);
v___x_630_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
lean_inc(v___x_615_);
v___x_631_ = l_Lean_MessageData_ofName(v___x_615_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_634_, v___y_596_, v___y_597_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_snd_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v_snd_637_ = lean_ctor_get(v_a_636_, 1);
lean_inc(v_snd_637_);
lean_dec(v_a_636_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v_snd_637_;
goto v___jp_599_;
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
lean_dec(v___x_615_);
v_a_638_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_635_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_635_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
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
case 1:
{
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v___y_595_;
goto v___jp_599_;
}
case 4:
{
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v___y_595_;
goto v___jp_599_;
}
case 3:
{
lean_del_object(v___x_619_);
lean_dec(v_val_617_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v___y_595_;
goto v___jp_599_;
}
default: 
{
lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_654_ = lean_unbox(v_val_617_);
lean_dec(v_val_617_);
v___x_655_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_654_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 3);
lean_ctor_set(v___x_619_, 0, v___x_655_);
v___x_657_ = v___x_619_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_677_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_658_ = l_Lean_MessageData_ofFormat(v___x_657_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_653_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc(v___x_615_);
v___x_662_ = l_Lean_MessageData_ofName(v___x_615_);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_606_, v___x_665_, v___y_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_595_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v_snd_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v_snd_668_ = lean_ctor_get(v_a_667_, 1);
lean_inc(v_snd_668_);
lean_dec(v_a_667_);
v_fst_600_ = v___x_615_;
v_snd_601_ = v_snd_668_;
goto v___jp_599_;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec(v___x_615_);
v_a_669_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_666_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_666_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
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
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_688_; 
lean_inc_ref(v_items_614_);
lean_inc(v_currKey_613_);
lean_inc(v_currArrKey_612_);
lean_inc(v_arrParents_611_);
lean_inc(v_arrKeyTys_610_);
lean_inc(v_keyTys_609_);
lean_dec(v___x_616_);
v_isSharedCheck_688_ = !lean_is_exclusive(v___y_595_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; lean_object* v_unused_692_; lean_object* v_unused_693_; lean_object* v_unused_694_; 
v_unused_689_ = lean_ctor_get(v___y_595_, 5);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v___y_595_, 4);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v___y_595_, 3);
lean_dec(v_unused_691_);
v_unused_692_ = lean_ctor_get(v___y_595_, 2);
lean_dec(v_unused_692_);
v_unused_693_ = lean_ctor_get(v___y_595_, 1);
lean_dec(v_unused_693_);
v_unused_694_ = lean_ctor_get(v___y_595_, 0);
lean_dec(v_unused_694_);
v___x_680_ = v___y_595_;
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
else
{
lean_dec(v___y_595_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_688_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_682_ = 4;
v___x_683_ = lean_box(v___x_682_);
lean_inc(v___x_615_);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_615_, v___x_683_, v_keyTys_609_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_684_);
v___x_686_ = v___x_680_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_arrKeyTys_610_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_arrParents_611_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_currArrKey_612_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_currKey_613_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v_items_614_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
v_fst_600_ = v___x_615_;
v_snd_601_ = v___x_686_;
goto v___jp_599_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v___y_595_);
lean_dec(v_b_594_);
v_a_695_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_607_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_607_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v_b_594_);
lean_ctor_set(v___x_703_, 1, v___y_595_);
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
v___jp_599_:
{
size_t v___x_602_; size_t v___x_603_; 
v___x_602_ = ((size_t)1ULL);
v___x_603_ = lean_usize_add(v_i_592_, v___x_602_);
v_i_592_ = v___x_603_;
v_b_594_ = v_fst_600_;
v___y_595_ = v_snd_601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___boxed(lean_object* v_as_705_, lean_object* v_i_706_, lean_object* v_stop_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
size_t v_i_boxed_713_; size_t v_stop_boxed_714_; lean_object* v_res_715_; 
v_i_boxed_713_ = lean_unbox_usize(v_i_706_);
lean_dec(v_i_706_);
v_stop_boxed_714_ = lean_unbox_usize(v_stop_707_);
lean_dec(v_stop_707_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_as_705_, v_i_boxed_713_, v_stop_boxed_714_, v_b_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec_ref(v_as_705_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(lean_object* v_t_716_, lean_object* v_k_717_){
_start:
{
if (lean_obj_tag(v_t_716_) == 0)
{
lean_object* v_k_718_; lean_object* v_v_719_; lean_object* v_l_720_; lean_object* v_r_721_; uint8_t v___x_722_; 
v_k_718_ = lean_ctor_get(v_t_716_, 1);
v_v_719_ = lean_ctor_get(v_t_716_, 2);
v_l_720_ = lean_ctor_get(v_t_716_, 3);
v_r_721_ = lean_ctor_get(v_t_716_, 4);
v___x_722_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_717_, v_k_718_);
switch(v___x_722_)
{
case 0:
{
v_t_716_ = v_l_720_;
goto _start;
}
case 1:
{
lean_object* v___x_724_; 
lean_inc(v_v_719_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v_v_719_);
return v___x_724_;
}
default: 
{
v_t_716_ = v_r_721_;
goto _start;
}
}
}
else
{
lean_object* v___x_726_; 
v___x_726_ = lean_box(0);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg___boxed(lean_object* v_t_727_, lean_object* v_k_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_727_, v_k_728_);
lean_dec(v_k_728_);
lean_dec(v_t_727_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(lean_object* v_ks_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_keyTys_735_; lean_object* v_arrKeyTys_736_; lean_object* v_arrParents_737_; lean_object* v_currArrKey_738_; lean_object* v_currKey_739_; lean_object* v_items_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_762_; 
v_keyTys_735_ = lean_ctor_get(v_a_731_, 0);
v_arrKeyTys_736_ = lean_ctor_get(v_a_731_, 1);
v_arrParents_737_ = lean_ctor_get(v_a_731_, 2);
v_currArrKey_738_ = lean_ctor_get(v_a_731_, 3);
v_currKey_739_ = lean_ctor_get(v_a_731_, 4);
v_items_740_ = lean_ctor_get(v_a_731_, 5);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_731_);
if (v_isSharedCheck_762_ == 0)
{
v___x_742_ = v_a_731_;
v_isShared_743_ = v_isSharedCheck_762_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_items_740_);
lean_inc(v_currKey_739_);
lean_inc(v_currArrKey_738_);
lean_inc(v_arrParents_737_);
lean_inc(v_arrKeyTys_736_);
lean_inc(v_keyTys_735_);
lean_dec(v_a_731_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_762_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_arrKeyTys_744_; lean_object* v___x_745_; lean_object* v___y_747_; lean_object* v___x_759_; 
v_arrKeyTys_744_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_738_, v_keyTys_735_, v_arrKeyTys_736_);
v___x_745_ = lean_box(0);
v___x_759_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_arrKeyTys_744_, v___x_745_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; 
v___x_760_ = lean_box(1);
v___y_747_ = v___x_760_;
goto v___jp_746_;
}
else
{
lean_object* v_val_761_; 
v_val_761_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v___x_759_, 1);
v___y_747_ = v_val_761_;
goto v___jp_746_;
}
v___jp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 3, v___x_745_);
lean_ctor_set(v___x_742_, 1, v_arrKeyTys_744_);
lean_ctor_set(v___x_742_, 0, v___y_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___y_747_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_arrKeyTys_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_arrParents_737_);
lean_ctor_set(v_reuseFailAlloc_758_, 3, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_758_, 4, v_currKey_739_);
lean_ctor_set(v_reuseFailAlloc_758_, 5, v_items_740_);
v___x_749_ = v_reuseFailAlloc_758_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_array_get_size(v_ks_730_);
v___x_752_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_745_);
lean_ctor_set(v___x_753_, 1, v___x_749_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_751_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0(v_ks_730_, v___x_755_, v___x_756_, v___x_745_, v___x_749_, v_a_732_, v_a_733_);
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys___boxed(lean_object* v_ks_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v_ks_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec_ref(v_ks_763_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(lean_object* v_00_u03b4_769_, lean_object* v_t_770_, lean_object* v_k_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___redArg(v_t_770_, v_k_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1___boxed(lean_object* v_00_u03b4_773_, lean_object* v_t_774_, lean_object* v_k_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__1(v_00_u03b4_773_, v_t_774_, v_k_775_);
lean_dec(v_k_775_);
lean_dec(v_t_774_);
return v_res_776_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0(void){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_777_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__3));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(lean_object* v_x_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___y_792_; lean_object* v_keyTys_793_; lean_object* v_arrKeyTys_794_; lean_object* v_arrParents_795_; lean_object* v_currArrKey_796_; lean_object* v_items_797_; lean_object* v_toCold_809_; lean_object* v_currRecDepth_810_; lean_object* v_ref_811_; uint16_t v_optionFlags_812_; uint8_t v_suppressElabErrors_813_; uint8_t v_checkDeprecated_814_; uint8_t v_isRecordingDeps_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v_ref_818_; lean_object* v___x_819_; 
v_toCold_809_ = lean_ctor_get(v_a_788_, 0);
v_currRecDepth_810_ = lean_ctor_get(v_a_788_, 1);
v_ref_811_ = lean_ctor_get(v_a_788_, 2);
v_optionFlags_812_ = lean_ctor_get_uint16(v_a_788_, sizeof(void*)*3);
v_suppressElabErrors_813_ = lean_ctor_get_uint8(v_a_788_, sizeof(void*)*3 + 2);
v_checkDeprecated_814_ = lean_ctor_get_uint8(v_a_788_, sizeof(void*)*3 + 3);
v_isRecordingDeps_815_ = lean_ctor_get_uint8(v_a_788_, sizeof(void*)*3 + 4);
v___x_816_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_786_);
v___x_817_ = l_Lean_Syntax_isOfKind(v_x_786_, v___x_816_);
v_ref_818_ = l_Lean_replaceRef(v_x_786_, v_ref_811_);
lean_inc(v_currRecDepth_810_);
lean_inc_ref(v_toCold_809_);
v___x_819_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_819_, 0, v_toCold_809_);
lean_ctor_set(v___x_819_, 1, v_currRecDepth_810_);
lean_ctor_set(v___x_819_, 2, v_ref_818_);
lean_ctor_set_uint16(v___x_819_, sizeof(void*)*3, v_optionFlags_812_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 2, v_suppressElabErrors_813_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 3, v_checkDeprecated_814_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*3 + 4, v_isRecordingDeps_815_);
if (v___x_817_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__4);
v___x_821_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_786_, v___x_820_, v_a_787_, v___x_819_, v_a_789_);
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_a_787_);
lean_dec(v_x_786_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___y_825_; lean_object* v___x_893_; uint8_t v___x_894_; 
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = l_Lean_Syntax_getArg(v_x_786_, v___x_822_);
v___x_893_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_823_);
v___x_894_ = l_Lean_Syntax_isOfKind(v___x_823_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec(v_x_786_);
v___x_895_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_896_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_823_, v___x_895_, v_a_787_, v___x_819_, v_a_789_);
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_a_787_);
lean_dec(v___x_823_);
return v___x_896_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = l_Lean_Syntax_getArg(v___x_823_, v___x_897_);
v___x_899_ = l_Lean_Syntax_getArgs(v___x_898_);
lean_dec(v___x_898_);
v___x_900_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_901_ = lean_array_get_size(v___x_899_);
v___x_902_ = lean_nat_dec_lt(v___x_897_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec_ref(v___x_899_);
v___y_825_ = v___x_900_;
goto v___jp_824_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; lean_object* v_snd_908_; 
v___x_903_ = lean_box(v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_900_);
v___x_905_ = ((size_t)0ULL);
v___x_906_ = lean_usize_of_nat(v___x_901_);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_894_, v___x_899_, v___x_905_, v___x_906_, v___x_904_);
lean_dec_ref(v___x_899_);
v_snd_908_ = lean_ctor_get(v___x_907_, 1);
lean_inc(v_snd_908_);
lean_dec_ref(v___x_907_);
v___y_825_ = v_snd_908_;
goto v___jp_824_;
}
}
v___jp_824_:
{
size_t v_sz_826_; size_t v___x_827_; lean_object* v___x_828_; 
v_sz_826_ = lean_array_size(v___y_825_);
v___x_827_ = ((size_t)0ULL);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_826_, v___x_827_, v___y_825_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v_x_786_);
v___x_829_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_830_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v___x_823_, v___x_829_, v_a_787_, v___x_819_, v_a_789_);
lean_dec_ref_known(v___x_819_, 3);
lean_dec_ref(v_a_787_);
lean_dec(v___x_823_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_tailKey_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec(v___x_823_);
v_val_831_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_828_, 1);
v___x_832_ = lean_box(0);
v___x_833_ = lean_array_get_size(v_val_831_);
v___x_834_ = lean_nat_sub(v___x_833_, v___x_822_);
v_tailKey_835_ = lean_array_get(v___x_832_, v_val_831_, v___x_834_);
lean_dec(v___x_834_);
v___x_836_ = lean_array_pop(v_val_831_);
v___x_837_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_836_, v_a_787_, v___x_819_, v_a_789_);
lean_dec_ref(v___x_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_884_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v_fst_839_ = lean_ctor_get(v_a_838_, 0);
v_snd_840_ = lean_ctor_get(v_a_838_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_884_ == 0)
{
v___x_842_ = v_a_838_;
v_isShared_843_ = v_isSharedCheck_884_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_snd_840_);
lean_inc(v_fst_839_);
lean_dec(v_a_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_884_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; 
lean_inc(v_tailKey_835_);
v___x_844_ = l_Lake_Toml_elabSimpleKey(v_tailKey_835_, v___x_819_, v_a_789_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v_keyTys_846_; lean_object* v_arrKeyTys_847_; lean_object* v_arrParents_848_; lean_object* v_currArrKey_849_; lean_object* v_items_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
v_keyTys_846_ = lean_ctor_get(v_snd_840_, 0);
v_arrKeyTys_847_ = lean_ctor_get(v_snd_840_, 1);
v_arrParents_848_ = lean_ctor_get(v_snd_840_, 2);
v_currArrKey_849_ = lean_ctor_get(v_snd_840_, 3);
v_items_850_ = lean_ctor_get(v_snd_840_, 5);
v___x_851_ = l_Lean_Name_str___override(v_fst_839_, v_a_845_);
v___x_852_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_846_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 1)
{
lean_object* v_val_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_875_; 
v_val_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_875_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_875_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_val_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_875_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
uint8_t v___x_857_; 
v___x_857_ = lean_unbox(v_val_853_);
if (v___x_857_ == 4)
{
lean_inc_ref(v_items_850_);
lean_inc(v_currArrKey_849_);
lean_inc(v_arrParents_848_);
lean_inc(v_arrKeyTys_847_);
lean_inc(v_keyTys_846_);
lean_del_object(v___x_855_);
lean_dec(v_val_853_);
lean_del_object(v___x_842_);
lean_dec(v_snd_840_);
lean_dec(v_tailKey_835_);
lean_dec_ref_known(v___x_819_, 3);
v___y_792_ = v___x_851_;
v_keyTys_793_ = v_keyTys_846_;
v_arrKeyTys_794_ = v_arrKeyTys_847_;
v_arrParents_795_ = v_arrParents_848_;
v_currArrKey_796_ = v_currArrKey_849_;
v_items_797_ = v_items_850_;
goto v___jp_791_;
}
else
{
lean_object* v___x_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_x_786_);
v___x_858_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__1);
v___x_859_ = lean_unbox(v_val_853_);
lean_dec(v_val_853_);
v___x_860_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_859_);
if (v_isShared_856_ == 0)
{
lean_ctor_set_tag(v___x_855_, 3);
lean_ctor_set(v___x_855_, 0, v___x_860_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_874_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = l_Lean_MessageData_ofFormat(v___x_862_);
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 7);
lean_ctor_set(v___x_842_, 1, v___x_863_);
lean_ctor_set(v___x_842_, 0, v___x_858_);
v___x_865_ = v___x_842_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_873_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_866_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__3);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_MessageData_ofName(v___x_851_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_835_, v___x_871_, v_snd_840_, v___x_819_, v_a_789_);
lean_dec_ref_known(v___x_819_, 3);
lean_dec(v_snd_840_);
lean_dec(v_tailKey_835_);
return v___x_872_;
}
}
}
}
}
else
{
lean_inc_ref(v_items_850_);
lean_inc(v_currArrKey_849_);
lean_inc(v_arrParents_848_);
lean_inc(v_arrKeyTys_847_);
lean_inc(v_keyTys_846_);
lean_dec(v___x_852_);
lean_del_object(v___x_842_);
lean_dec(v_snd_840_);
lean_dec(v_tailKey_835_);
lean_dec_ref_known(v___x_819_, 3);
v___y_792_ = v___x_851_;
v_keyTys_793_ = v_keyTys_846_;
v_arrKeyTys_794_ = v_arrKeyTys_847_;
v_arrParents_795_ = v_arrParents_848_;
v_currArrKey_796_ = v_currArrKey_849_;
v_items_797_ = v_items_850_;
goto v___jp_791_;
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_del_object(v___x_842_);
lean_dec(v_snd_840_);
lean_dec(v_fst_839_);
lean_dec(v_tailKey_835_);
lean_dec_ref_known(v___x_819_, 3);
lean_dec(v_x_786_);
v_a_876_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_844_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_844_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
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
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_tailKey_835_);
lean_dec_ref_known(v___x_819_, 3);
lean_dec(v_x_786_);
v_a_885_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_837_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_837_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
v___jp_791_:
{
lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_798_ = lean_box(0);
v___x_799_ = 1;
v___x_800_ = lean_box(v___x_799_);
lean_inc_n(v___y_792_, 2);
v___x_801_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___y_792_, v___x_800_, v_keyTys_793_);
v___x_802_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_x_786_);
v___x_803_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_803_, 0, v_x_786_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_804_, 0, v_x_786_);
lean_ctor_set(v___x_804_, 1, v___y_792_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
v___x_805_ = lean_array_push(v_items_797_, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_806_, 0, v___x_801_);
lean_ctor_set(v___x_806_, 1, v_arrKeyTys_794_);
lean_ctor_set(v___x_806_, 2, v_arrParents_795_);
lean_ctor_set(v___x_806_, 3, v_currArrKey_796_);
lean_ctor_set(v___x_806_, 4, v___y_792_);
lean_ctor_set(v___x_806_, 5, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_798_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___boxed(lean_object* v_x_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_909_, v_a_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_914_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__2));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(lean_object* v_x_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_toCold_928_; lean_object* v_currRecDepth_929_; lean_object* v_ref_930_; uint16_t v_optionFlags_931_; uint8_t v_suppressElabErrors_932_; uint8_t v_checkDeprecated_933_; uint8_t v_isRecordingDeps_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v_ref_937_; lean_object* v___x_938_; lean_object* v___y_940_; 
v_toCold_928_ = lean_ctor_get(v_a_925_, 0);
v_currRecDepth_929_ = lean_ctor_get(v_a_925_, 1);
v_ref_930_ = lean_ctor_get(v_a_925_, 2);
v_optionFlags_931_ = lean_ctor_get_uint16(v_a_925_, sizeof(void*)*3);
v_suppressElabErrors_932_ = lean_ctor_get_uint8(v_a_925_, sizeof(void*)*3 + 2);
v_checkDeprecated_933_ = lean_ctor_get_uint8(v_a_925_, sizeof(void*)*3 + 3);
v_isRecordingDeps_934_ = lean_ctor_get_uint8(v_a_925_, sizeof(void*)*3 + 4);
v___x_935_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_923_);
v___x_936_ = l_Lean_Syntax_isOfKind(v_x_923_, v___x_935_);
v_ref_937_ = l_Lean_replaceRef(v_x_923_, v_ref_930_);
lean_inc(v_currRecDepth_929_);
lean_inc_ref(v_toCold_928_);
v___x_938_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_938_, 0, v_toCold_928_);
lean_ctor_set(v___x_938_, 1, v_currRecDepth_929_);
lean_ctor_set(v___x_938_, 2, v_ref_937_);
lean_ctor_set_uint16(v___x_938_, sizeof(void*)*3, v_optionFlags_931_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*3 + 2, v_suppressElabErrors_932_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*3 + 3, v_checkDeprecated_933_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*3 + 4, v_isRecordingDeps_934_);
if (v___x_936_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__3);
v___x_948_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_923_, v___x_947_, v_a_924_, v___x_938_, v_a_926_);
lean_dec_ref_known(v___x_938_, 3);
lean_dec_ref(v_a_924_);
lean_dec(v_x_923_);
return v___x_948_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___y_954_; 
v___x_949_ = lean_unsigned_to_nat(2u);
v___x_950_ = l_Lean_Syntax_getArg(v_x_923_, v___x_949_);
v___x_951_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__5));
lean_inc(v___x_950_);
v___x_952_ = l_Lean_Syntax_isOfKind(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v___x_950_);
v___x_1088_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_1089_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_923_, v___x_1088_, v_a_924_, v___x_938_, v_a_926_);
lean_dec_ref_known(v___x_938_, 3);
lean_dec_ref(v_a_924_);
lean_dec(v_x_923_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = l_Lean_Syntax_getArg(v___x_950_, v___x_1090_);
lean_dec(v___x_950_);
v___x_1092_ = l_Lean_Syntax_getArgs(v___x_1091_);
lean_dec(v___x_1091_);
v___x_1093_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__8));
v___x_1094_ = lean_array_get_size(v___x_1092_);
v___x_1095_ = lean_nat_dec_lt(v___x_1090_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_dec_ref(v___x_1092_);
v___y_954_ = v___x_1093_;
goto v___jp_953_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v___x_1100_; lean_object* v_snd_1101_; 
v___x_1096_ = lean_box(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1093_);
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = lean_usize_of_nat(v___x_1094_);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__1(v___x_952_, v___x_1092_, v___x_1098_, v___x_1099_, v___x_1097_);
lean_dec_ref(v___x_1092_);
v_snd_1101_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_snd_1101_);
lean_dec_ref(v___x_1100_);
v___y_954_ = v_snd_1101_;
goto v___jp_953_;
}
}
v___jp_953_:
{
size_t v_sz_955_; size_t v___x_956_; lean_object* v___x_957_; 
v_sz_955_ = lean_array_size(v___y_954_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval_spec__0(v_sz_955_, v___x_956_, v___y_954_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__7);
v___x_959_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_923_, v___x_958_, v_a_924_, v___x_938_, v_a_926_);
lean_dec_ref_known(v___x_938_, 3);
lean_dec_ref(v_a_924_);
lean_dec(v_x_923_);
return v___x_959_;
}
else
{
lean_object* v_val_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_tailKey_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_val_960_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_val_960_);
lean_dec_ref_known(v___x_957_, 1);
v___x_961_ = lean_box(0);
v___x_962_ = lean_array_get_size(v_val_960_);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = lean_nat_sub(v___x_962_, v___x_963_);
v_tailKey_965_ = lean_array_get(v___x_961_, v_val_960_, v___x_964_);
lean_dec(v___x_964_);
v___x_966_ = lean_array_pop(v_val_960_);
v___x_967_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys(v___x_966_, v_a_924_, v___x_938_, v_a_926_);
lean_dec_ref(v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v_fst_969_; lean_object* v_snd_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1079_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_967_, 1);
v_fst_969_ = lean_ctor_get(v_a_968_, 0);
v_snd_970_ = lean_ctor_get(v_a_968_, 1);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_a_968_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_972_ = v_a_968_;
v_isShared_973_ = v_isSharedCheck_1079_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_snd_970_);
lean_inc(v_fst_969_);
lean_dec(v_a_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1079_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; 
lean_inc(v_tailKey_965_);
v___x_974_ = l_Lake_Toml_elabSimpleKey(v_tailKey_965_, v___x_938_, v_a_926_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1070_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1070_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1070_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_keyTys_979_; lean_object* v_arrKeyTys_980_; lean_object* v_arrParents_981_; lean_object* v_currArrKey_982_; lean_object* v_items_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_keyTys_979_ = lean_ctor_get(v_snd_970_, 0);
v_arrKeyTys_980_ = lean_ctor_get(v_snd_970_, 1);
v_arrParents_981_ = lean_ctor_get(v_snd_970_, 2);
v_currArrKey_982_ = lean_ctor_get(v_snd_970_, 3);
v_items_983_ = lean_ctor_get(v_snd_970_, 5);
v___x_984_ = l_Lean_Name_str___override(v_fst_969_, v_a_975_);
v___x_985_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_keyTys_979_, v___x_984_);
if (lean_obj_tag(v___x_985_) == 1)
{
lean_object* v_val_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1037_; 
v_val_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1037_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_val_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1037_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = lean_unbox(v_val_986_);
if (v___x_990_ == 2)
{
lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1015_; 
lean_inc_ref(v_items_983_);
lean_inc(v_arrParents_981_);
lean_inc(v_arrKeyTys_980_);
lean_del_object(v___x_988_);
lean_dec(v_val_986_);
lean_dec(v_tailKey_965_);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_snd_970_);
if (v_isSharedCheck_1015_ == 0)
{
lean_object* v_unused_1016_; lean_object* v_unused_1017_; lean_object* v_unused_1018_; lean_object* v_unused_1019_; lean_object* v_unused_1020_; lean_object* v_unused_1021_; 
v_unused_1016_ = lean_ctor_get(v_snd_970_, 5);
lean_dec(v_unused_1016_);
v_unused_1017_ = lean_ctor_get(v_snd_970_, 4);
lean_dec(v_unused_1017_);
v_unused_1018_ = lean_ctor_get(v_snd_970_, 3);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_snd_970_, 2);
lean_dec(v_unused_1019_);
v_unused_1020_ = lean_ctor_get(v_snd_970_, 1);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_snd_970_, 0);
lean_dec(v_unused_1021_);
v___x_992_ = v_snd_970_;
v_isShared_993_ = v_isSharedCheck_1015_;
goto v_resetjp_991_;
}
else
{
lean_dec(v_snd_970_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1015_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrParents_981_, v___x_984_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_del_object(v___x_992_);
lean_dec_ref(v_items_983_);
lean_dec(v_arrParents_981_);
lean_dec(v_arrKeyTys_980_);
lean_del_object(v___x_977_);
lean_del_object(v___x_972_);
lean_dec(v_x_923_);
v___y_940_ = v___x_984_;
goto v___jp_939_;
}
else
{
lean_object* v_val_995_; lean_object* v___x_996_; 
v_val_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_arrKeyTys_980_, v_val_995_);
lean_dec(v_val_995_);
if (lean_obj_tag(v___x_996_) == 1)
{
lean_object* v_val_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_dec_ref_known(v___x_938_, 3);
v_val_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_val_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = lean_box(0);
v___x_999_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_923_, 2);
v___x_1000_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_x_923_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_963_);
v___x_1002_ = lean_array_push(v___x_1001_, v___x_1000_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_x_923_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
lean_inc_n(v___x_984_, 2);
v___x_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_x_923_);
lean_ctor_set(v___x_1004_, 1, v___x_984_);
lean_ctor_set(v___x_1004_, 2, v___x_1003_);
v___x_1005_ = lean_array_push(v_items_983_, v___x_1004_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 5, v___x_1005_);
lean_ctor_set(v___x_992_, 4, v___x_984_);
lean_ctor_set(v___x_992_, 3, v___x_984_);
lean_ctor_set(v___x_992_, 0, v_val_997_);
v___x_1007_ = v___x_992_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_val_997_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_arrKeyTys_980_);
lean_ctor_set(v_reuseFailAlloc_1014_, 2, v_arrParents_981_);
lean_ctor_set(v_reuseFailAlloc_1014_, 3, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_1014_, 4, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_1014_, 5, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_1007_);
lean_ctor_set(v___x_972_, 0, v___x_998_);
v___x_1009_ = v___x_972_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_1009_);
v___x_1011_ = v___x_977_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_dec(v___x_996_);
lean_del_object(v___x_992_);
lean_dec_ref(v_items_983_);
lean_dec(v_arrParents_981_);
lean_dec(v_arrKeyTys_980_);
lean_del_object(v___x_977_);
lean_del_object(v___x_972_);
lean_dec(v_x_923_);
v___y_940_ = v___x_984_;
goto v___jp_939_;
}
}
}
}
else
{
lean_object* v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_del_object(v___x_977_);
lean_del_object(v___x_972_);
lean_dec(v_x_923_);
v___x_1022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__0));
v___x_1023_ = lean_unbox(v_val_986_);
lean_dec(v_val_986_);
v___x_1024_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_KeyTy_toString(v___x_1023_);
v___x_1025_ = lean_string_append(v___x_1022_, v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__2));
v___x_1027_ = lean_string_append(v___x_1025_, v___x_1026_);
v___x_1028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_984_, v___x_952_);
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__4));
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
if (v_isShared_989_ == 0)
{
lean_ctor_set_tag(v___x_988_, 3);
lean_ctor_set(v___x_988_, 0, v___x_1031_);
v___x_1033_ = v___x_988_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = l_Lean_MessageData_ofFormat(v___x_1033_);
v___x_1035_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_tailKey_965_, v___x_1034_, v_snd_970_, v___x_938_, v_a_926_);
lean_dec_ref_known(v___x_938_, 3);
lean_dec(v_snd_970_);
lean_dec(v_tailKey_965_);
return v___x_1035_;
}
}
}
}
else
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1063_; 
lean_inc_ref(v_items_983_);
lean_inc(v_currArrKey_982_);
lean_inc(v_arrParents_981_);
lean_inc(v_arrKeyTys_980_);
lean_inc(v_keyTys_979_);
lean_dec(v___x_985_);
lean_dec(v_tailKey_965_);
lean_dec_ref_known(v___x_938_, 3);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_snd_970_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; lean_object* v_unused_1065_; lean_object* v_unused_1066_; lean_object* v_unused_1067_; lean_object* v_unused_1068_; lean_object* v_unused_1069_; 
v_unused_1064_ = lean_ctor_get(v_snd_970_, 5);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_snd_970_, 4);
lean_dec(v_unused_1065_);
v_unused_1066_ = lean_ctor_get(v_snd_970_, 3);
lean_dec(v_unused_1066_);
v_unused_1067_ = lean_ctor_get(v_snd_970_, 2);
lean_dec(v_unused_1067_);
v_unused_1068_ = lean_ctor_get(v_snd_970_, 1);
lean_dec(v_unused_1068_);
v_unused_1069_ = lean_ctor_get(v_snd_970_, 0);
lean_dec(v_unused_1069_);
v___x_1039_ = v_snd_970_;
v_isShared_1040_ = v_isSharedCheck_1063_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v_snd_970_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1063_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = 2;
v___x_1043_ = lean_box(v___x_1042_);
lean_inc_n(v___x_984_, 4);
v___x_1044_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_984_, v___x_1043_, v_keyTys_979_);
lean_inc(v___x_1044_);
lean_inc(v_currArrKey_982_);
v___x_1045_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_currArrKey_982_, v___x_1044_, v_arrKeyTys_980_);
v___x_1046_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_984_, v_currArrKey_982_, v_arrParents_981_);
v___x_1047_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc_n(v_x_923_, 2);
v___x_1048_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1048_, 0, v_x_923_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_mk_empty_array_with_capacity(v___x_963_);
v___x_1050_ = lean_array_push(v___x_1049_, v___x_1048_);
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_x_923_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1052_, 0, v_x_923_);
lean_ctor_set(v___x_1052_, 1, v___x_984_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
v___x_1053_ = lean_array_push(v_items_983_, v___x_1052_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 5, v___x_1053_);
lean_ctor_set(v___x_1039_, 4, v___x_984_);
lean_ctor_set(v___x_1039_, 3, v___x_984_);
lean_ctor_set(v___x_1039_, 2, v___x_1046_);
lean_ctor_set(v___x_1039_, 1, v___x_1045_);
lean_ctor_set(v___x_1039_, 0, v___x_1044_);
v___x_1055_ = v___x_1039_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_1062_, 5, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_1055_);
lean_ctor_set(v___x_972_, 0, v___x_1041_);
v___x_1057_ = v___x_972_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_1057_);
v___x_1059_ = v___x_977_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_972_);
lean_dec(v_snd_970_);
lean_dec(v_fst_969_);
lean_dec(v_tailKey_965_);
lean_dec_ref_known(v___x_938_, 3);
lean_dec(v_x_923_);
v_a_1071_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_974_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_974_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec(v_tailKey_965_);
lean_dec_ref_known(v___x_938_, 3);
lean_dec(v_x_923_);
v_a_1080_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_967_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_967_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
v___jp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_941_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabHeaderKeys_spec__0___closed__1);
v___x_942_ = l_Lean_MessageData_ofName(v___y_940_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__1___closed__5);
v___x_945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0___redArg(v___x_945_, v___x_938_, v_a_926_);
lean_dec_ref_known(v___x_938_, 3);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___boxed(lean_object* v_x_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
return v_res_1107_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__0));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(lean_object* v_x_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_x_1111_);
v___x_1117_ = l_Lean_Syntax_isOfKind(v_x_1111_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_x_1111_);
v___x_1119_ = l_Lean_Syntax_isOfKind(v_x_1111_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_x_1111_);
v___x_1121_ = l_Lean_Syntax_isOfKind(v_x_1111_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___closed__1);
v___x_1123_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0___redArg(v_x_1111_, v___x_1122_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec_ref(v_a_1112_);
lean_dec(v_x_1111_);
return v___x_1123_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_x_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1124_;
}
}
else
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_x_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1125_;
}
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_x_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression___boxed(lean_object* v_x_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabExpression(v_x_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(lean_object* v_ref_1134_, lean_object* v_as_1135_, size_t v_i_1136_, size_t v_stop_1137_, lean_object* v_b_1138_){
_start:
{
lean_object* v___y_1140_; uint8_t v___x_1144_; 
v___x_1144_ = lean_usize_dec_eq(v_i_1136_, v_stop_1137_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v_fst_1146_; lean_object* v_snd_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_array_uget_borrowed(v_as_1135_, v_i_1136_);
v_fst_1146_ = lean_ctor_get(v___x_1145_, 0);
v_snd_1147_ = lean_ctor_get(v___x_1145_, 1);
lean_inc(v_fst_1146_);
v___x_1148_ = l_Lean_Name_components(v_fst_1146_);
if (lean_obj_tag(v___x_1148_) == 0)
{
v___y_1140_ = v_b_1138_;
goto v___jp_1139_;
}
else
{
lean_object* v_head_1149_; lean_object* v_tail_1150_; lean_object* v___x_1151_; 
v_head_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_head_1149_);
v_tail_1150_ = lean_ctor_get(v___x_1148_, 1);
lean_inc(v_tail_1150_);
lean_dec_ref_known(v___x_1148_, 2);
lean_inc(v_snd_1147_);
lean_inc(v_ref_1134_);
v___x_1151_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1138_, v_ref_1134_, v_head_1149_, v_tail_1150_, v_snd_1147_);
v___y_1140_ = v___x_1151_;
goto v___jp_1139_;
}
}
else
{
lean_dec(v_ref_1134_);
return v_b_1138_;
}
v___jp_1139_:
{
size_t v___x_1141_; size_t v___x_1142_; 
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1136_, v___x_1141_);
v_i_1136_ = v___x_1142_;
v_b_1138_ = v___y_1140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(size_t v_sz_1152_, size_t v_i_1153_, lean_object* v_bs_1154_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1153_, v_sz_1152_);
if (v___x_1155_ == 0)
{
return v_bs_1154_;
}
else
{
lean_object* v_v_1156_; lean_object* v___x_1157_; lean_object* v_bs_x27_1158_; lean_object* v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
v_v_1156_ = lean_array_uget(v_bs_1154_, v_i_1153_);
v___x_1157_ = lean_unsigned_to_nat(0u);
v_bs_x27_1158_ = lean_array_uset(v_bs_1154_, v_i_1153_, v___x_1157_);
v___x_1159_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_v_1156_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1153_, v___x_1160_);
v___x_1162_ = lean_array_uset(v_bs_x27_1158_, v_i_1153_, v___x_1159_);
v_i_1153_ = v___x_1161_;
v_bs_1154_ = v___x_1162_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(lean_object* v_a_1164_){
_start:
{
switch(lean_obj_tag(v_a_1164_))
{
case 6:
{
lean_object* v_xs_1165_; lean_object* v_ref_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1184_; 
v_xs_1165_ = lean_ctor_get(v_a_1164_, 1);
v_ref_1166_ = lean_ctor_get(v_a_1164_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1168_ = v_a_1164_;
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_xs_1165_);
lean_inc(v_ref_1166_);
lean_dec(v_a_1164_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1184_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_items_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_items_1170_ = lean_ctor_get(v_xs_1165_, 0);
lean_inc_ref(v_items_1170_);
lean_dec_ref(v_xs_1165_);
v___x_1171_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = lean_array_get_size(v_items_1170_);
v___x_1174_ = lean_nat_dec_lt(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_items_1170_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1171_);
v___x_1176_ = v___x_1168_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_ref_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
else
{
size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1178_ = ((size_t)0ULL);
v___x_1179_ = lean_usize_of_nat(v___x_1173_);
lean_inc(v_ref_1166_);
v___x_1180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1166_, v_items_1170_, v___x_1178_, v___x_1179_, v___x_1171_);
lean_dec_ref(v_items_1170_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1180_);
v___x_1182_ = v___x_1168_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_ref_1166_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
case 5:
{
lean_object* v_ref_1185_; lean_object* v_xs_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1196_; 
v_ref_1185_ = lean_ctor_get(v_a_1164_, 0);
v_xs_1186_ = lean_ctor_get(v_a_1164_, 1);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_a_1164_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1188_ = v_a_1164_;
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_xs_1186_);
lean_inc(v_ref_1185_);
lean_dec(v_a_1164_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1196_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
size_t v_sz_1190_; size_t v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
v_sz_1190_ = lean_array_size(v_xs_1186_);
v___x_1191_ = ((size_t)0ULL);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_1190_, v___x_1191_, v_xs_1186_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___x_1192_);
v___x_1194_ = v___x_1188_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_ref_1185_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1192_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
default: 
{
return v_a_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(lean_object* v_newV_1197_, lean_object* v___x_1198_, lean_object* v_v_x3f_1199_){
_start:
{
if (lean_obj_tag(v_v_x3f_1199_) == 1)
{
lean_object* v_val_1200_; 
v_val_1200_ = lean_ctor_get(v_v_x3f_1199_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_v_x3f_1199_, 1);
switch(lean_obj_tag(v_val_1200_))
{
case 6:
{
lean_object* v_ref_1201_; lean_object* v_xs_1202_; lean_object* v___x_1203_; 
v_ref_1201_ = lean_ctor_get(v_val_1200_, 0);
lean_inc(v_ref_1201_);
v_xs_1202_ = lean_ctor_get(v_val_1200_, 1);
lean_inc_ref(v_xs_1202_);
lean_dec_ref_known(v_val_1200_, 2);
v___x_1203_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1197_);
if (lean_obj_tag(v___x_1203_) == 6)
{
lean_object* v_xs_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1213_; 
v_xs_1204_ = lean_ctor_get(v___x_1203_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; 
v_unused_1214_ = lean_ctor_get(v___x_1203_, 0);
lean_dec(v_unused_1214_);
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_xs_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1213_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_items_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v_items_1208_ = lean_ctor_get(v_xs_1204_, 0);
lean_inc_ref(v_items_1208_);
lean_dec_ref(v_xs_1204_);
v___x_1209_ = l_Lake_Toml_RBDict_appendArray___redArg(v___x_1198_, v_xs_1202_, v_items_1208_);
lean_dec_ref(v_items_1208_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v___x_1209_);
lean_ctor_set(v___x_1206_, 0, v_ref_1201_);
v___x_1211_ = v___x_1206_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_ref_1201_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_dec_ref(v_xs_1202_);
lean_dec(v_ref_1201_);
lean_dec_ref(v___x_1198_);
return v___x_1203_;
}
}
case 5:
{
lean_object* v_ref_1215_; lean_object* v_xs_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v___x_1198_);
v_ref_1215_ = lean_ctor_get(v_val_1200_, 0);
v_xs_1216_ = lean_ctor_get(v_val_1200_, 1);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_val_1200_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1218_ = v_val_1200_;
v_isShared_1219_ = v_isSharedCheck_1235_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_xs_1216_);
lean_inc(v_ref_1215_);
lean_dec(v_val_1200_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1235_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; 
v___x_1220_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1197_);
if (lean_obj_tag(v___x_1220_) == 5)
{
lean_object* v_xs_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1229_; 
lean_del_object(v___x_1218_);
v_xs_1221_ = lean_ctor_get(v___x_1220_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1220_, 0);
lean_dec(v_unused_1230_);
v___x_1223_ = v___x_1220_;
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_xs_1221_);
lean_dec(v___x_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1229_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = l_Array_append___redArg(v_xs_1216_, v_xs_1221_);
lean_dec_ref(v_xs_1221_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 1, v___x_1225_);
lean_ctor_set(v___x_1223_, 0, v_ref_1215_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_ref_1215_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_array_push(v_xs_1216_, v___x_1220_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1231_);
v___x_1233_ = v___x_1218_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_ref_1215_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1231_);
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
default: 
{
lean_object* v___x_1236_; 
lean_dec(v_val_1200_);
lean_dec_ref(v___x_1198_);
v___x_1236_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1197_);
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1237_; 
lean_dec(v_v_x3f_1199_);
lean_dec_ref(v___x_1198_);
v___x_1237_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal(v_newV_1197_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(lean_object* v_newV_1238_, lean_object* v_k_1239_, lean_object* v_t_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1240_);
lean_inc(v_k_1239_);
v___x_1242_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1241_, v_k_1239_, v_t_1240_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_k_1239_);
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1278_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_val_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1278_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_items_1247_; lean_object* v_indices_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1277_; 
v_items_1247_ = lean_ctor_get(v_t_1240_, 0);
v_indices_1248_ = lean_ctor_get(v_t_1240_, 1);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_t_1240_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1250_ = v_t_1240_;
v_isShared_1251_ = v_isSharedCheck_1277_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_indices_1248_);
lean_inc(v_items_1247_);
lean_dec(v_t_1240_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1277_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_items_1247_);
v___x_1253_ = lean_nat_dec_lt(v_val_1243_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1255_; 
lean_del_object(v___x_1245_);
lean_dec(v_val_1243_);
lean_dec_ref(v_newV_1238_);
if (v_isShared_1251_ == 0)
{
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_items_1247_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_indices_1248_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v_v_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1276_; 
v_v_1257_ = lean_array_fget(v_items_1247_, v_val_1243_);
v_fst_1258_ = lean_ctor_get(v_v_1257_, 0);
v_snd_1259_ = lean_ctor_get(v_v_1257_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_v_1257_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1261_ = v_v_1257_;
v_isShared_1262_ = v_isSharedCheck_1276_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1258_);
lean_dec(v_v_1257_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1276_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1263_; lean_object* v_xs_x27_1264_; lean_object* v___x_1266_; 
v___x_1263_ = lean_box(0);
v_xs_x27_1264_ = lean_array_fset(v_items_1247_, v_val_1243_, v___x_1263_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_snd_1259_);
v___x_1266_ = v___x_1245_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_snd_1259_);
v___x_1266_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1238_, v___x_1241_, v___x_1266_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1267_);
v___x_1269_ = v___x_1261_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_fst_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_array_fset(v_xs_x27_1264_, v_val_1243_, v___x_1269_);
lean_dec(v_val_1243_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1270_);
v___x_1272_ = v___x_1250_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_indices_1248_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
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
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v___x_1242_);
v___x_1279_ = lean_box(0);
v___x_1280_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___lam__0(v_newV_1238_, v___x_1241_, v___x_1279_);
v___x_1281_ = l_Lake_Toml_RBDict_push___redArg(v___x_1241_, v_k_1239_, v___x_1280_, v_t_1240_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(lean_object* v_kRef_1282_, lean_object* v_head_1283_, lean_object* v_tail_1284_, lean_object* v_newV_1285_, lean_object* v_v_x3f_1286_){
_start:
{
if (lean_obj_tag(v_v_x3f_1286_) == 1)
{
lean_object* v_val_1287_; 
v_val_1287_ = lean_ctor_get(v_v_x3f_1286_, 0);
lean_inc(v_val_1287_);
lean_dec_ref_known(v_v_x3f_1286_, 1);
switch(lean_obj_tag(v_val_1287_))
{
case 5:
{
lean_object* v_ref_1288_; lean_object* v_xs_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_ref_1288_ = lean_ctor_get(v_val_1287_, 0);
v_xs_1289_ = lean_ctor_get(v_val_1287_, 1);
v___x_1290_ = lean_array_get_size(v_xs_1289_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_sub(v___x_1290_, v___x_1291_);
v___x_1293_ = lean_nat_dec_lt(v___x_1292_, v___x_1290_);
if (v___x_1293_ == 0)
{
lean_dec(v___x_1292_);
lean_dec_ref(v_newV_1285_);
lean_dec(v_tail_1284_);
lean_dec(v_head_1283_);
lean_dec(v_kRef_1282_);
return v_val_1287_;
}
else
{
lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1318_; 
lean_inc_ref(v_xs_1289_);
lean_inc(v_ref_1288_);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_val_1287_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; lean_object* v_unused_1320_; 
v_unused_1319_ = lean_ctor_get(v_val_1287_, 1);
lean_dec(v_unused_1319_);
v_unused_1320_ = lean_ctor_get(v_val_1287_, 0);
lean_dec(v_unused_1320_);
v___x_1295_ = v_val_1287_;
v_isShared_1296_ = v_isSharedCheck_1318_;
goto v_resetjp_1294_;
}
else
{
lean_dec(v_val_1287_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1318_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v_v_1297_; lean_object* v___x_1298_; lean_object* v_xs_x27_1299_; lean_object* v___y_1301_; 
v_v_1297_ = lean_array_fget(v_xs_1289_, v___x_1292_);
v___x_1298_ = lean_box(0);
v_xs_x27_1299_ = lean_array_fset(v_xs_1289_, v___x_1292_, v___x_1298_);
if (lean_obj_tag(v_v_1297_) == 6)
{
lean_object* v_ref_1306_; lean_object* v_xs_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1315_; 
v_ref_1306_ = lean_ctor_get(v_v_1297_, 0);
v_xs_1307_ = lean_ctor_get(v_v_1297_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_v_1297_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1309_ = v_v_1297_;
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_xs_1307_);
lean_inc(v_ref_1306_);
lean_dec(v_v_1297_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1315_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1307_, v_kRef_1282_, v_head_1283_, v_tail_1284_, v_newV_1285_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___x_1311_);
v___x_1313_ = v___x_1309_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_ref_1306_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
v___y_1301_ = v___x_1313_;
goto v___jp_1300_;
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec(v_v_1297_);
lean_dec_ref(v_newV_1285_);
lean_dec(v_tail_1284_);
lean_dec(v_head_1283_);
v___x_1316_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1317_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1317_, 0, v_kRef_1282_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___y_1301_ = v___x_1317_;
goto v___jp_1300_;
}
v___jp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_array_fset(v_xs_x27_1299_, v___x_1292_, v___y_1301_);
lean_dec(v___x_1292_);
if (v_isShared_1296_ == 0)
{
lean_ctor_set(v___x_1295_, 1, v___x_1302_);
v___x_1304_ = v___x_1295_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_ref_1288_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
}
case 6:
{
lean_object* v_ref_1321_; lean_object* v_xs_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_ref_1321_ = lean_ctor_get(v_val_1287_, 0);
v_xs_1322_ = lean_ctor_get(v_val_1287_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_val_1287_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1324_ = v_val_1287_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_xs_1322_);
lean_inc(v_ref_1321_);
lean_dec(v_val_1287_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_xs_1322_, v_kRef_1282_, v_head_1283_, v_tail_1284_, v_newV_1285_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_ref_1321_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
default: 
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_val_1287_);
v___x_1331_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1282_);
v___x_1332_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1331_, v_kRef_1282_, v_head_1283_, v_tail_1284_, v_newV_1285_);
v___x_1333_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_kRef_1282_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
return v___x_1333_;
}
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_v_x3f_1286_);
v___x_1334_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
lean_inc(v_kRef_1282_);
v___x_1335_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v___x_1334_, v_kRef_1282_, v_head_1283_, v_tail_1284_, v_newV_1285_);
v___x_1336_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_kRef_1282_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(lean_object* v_kRef_1337_, lean_object* v_head_1338_, lean_object* v_tail_1339_, lean_object* v_newV_1340_, lean_object* v_k_1341_, lean_object* v_t_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = ((lean_object*)(l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3___closed__0));
lean_inc_ref(v_t_1342_);
lean_inc(v_k_1341_);
v___x_1344_ = l_Lake_Toml_RBDict_findIdx_x3f___redArg(v___x_1343_, v_k_1341_, v_t_1342_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v_k_1341_);
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1380_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_val_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1380_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v_items_1349_; lean_object* v_indices_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1379_; 
v_items_1349_ = lean_ctor_get(v_t_1342_, 0);
v_indices_1350_ = lean_ctor_get(v_t_1342_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_t_1342_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1352_ = v_t_1342_;
v_isShared_1353_ = v_isSharedCheck_1379_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_indices_1350_);
lean_inc(v_items_1349_);
lean_dec(v_t_1342_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1379_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1354_ = lean_array_get_size(v_items_1349_);
v___x_1355_ = lean_nat_dec_lt(v_val_1345_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1357_; 
lean_del_object(v___x_1347_);
lean_dec(v_val_1345_);
lean_dec_ref(v_newV_1340_);
lean_dec(v_tail_1339_);
lean_dec(v_head_1338_);
lean_dec(v_kRef_1337_);
if (v_isShared_1353_ == 0)
{
v___x_1357_ = v___x_1352_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_items_1349_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_indices_1350_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
else
{
lean_object* v_v_1359_; lean_object* v_fst_1360_; lean_object* v_snd_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1378_; 
v_v_1359_ = lean_array_fget(v_items_1349_, v_val_1345_);
v_fst_1360_ = lean_ctor_get(v_v_1359_, 0);
v_snd_1361_ = lean_ctor_get(v_v_1359_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_v_1359_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1363_ = v_v_1359_;
v_isShared_1364_ = v_isSharedCheck_1378_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_snd_1361_);
lean_inc(v_fst_1360_);
lean_dec(v_v_1359_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1378_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v_xs_x27_1366_; lean_object* v___x_1368_; 
v___x_1365_ = lean_box(0);
v_xs_x27_1366_ = lean_array_fset(v_items_1349_, v_val_1345_, v___x_1365_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v_snd_1361_);
v___x_1368_ = v___x_1347_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_snd_1361_);
v___x_1368_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1337_, v_head_1338_, v_tail_1339_, v_newV_1340_, v___x_1368_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v___x_1369_);
v___x_1371_ = v___x_1363_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_fst_1360_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = lean_array_fset(v_xs_x27_1366_, v_val_1345_, v___x_1371_);
lean_dec(v_val_1345_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1372_);
v___x_1374_ = v___x_1352_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_indices_1350_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
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
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v___x_1344_);
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4___lam__0(v_kRef_1337_, v_head_1338_, v_tail_1339_, v_newV_1340_, v___x_1381_);
v___x_1383_ = l_Lake_Toml_RBDict_push___redArg(v___x_1343_, v_k_1341_, v___x_1382_, v_t_1342_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(lean_object* v_t_1384_, lean_object* v_kRef_1385_, lean_object* v_k_1386_, lean_object* v_ks_1387_, lean_object* v_newV_1388_){
_start:
{
if (lean_obj_tag(v_ks_1387_) == 0)
{
lean_object* v___x_1389_; 
lean_dec(v_kRef_1385_);
v___x_1389_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__3(v_newV_1388_, v_k_1386_, v_t_1384_);
return v___x_1389_;
}
else
{
lean_object* v_head_1390_; lean_object* v_tail_1391_; lean_object* v___x_1392_; 
v_head_1390_ = lean_ctor_get(v_ks_1387_, 0);
lean_inc(v_head_1390_);
v_tail_1391_ = lean_ctor_get(v_ks_1387_, 1);
lean_inc(v_tail_1391_);
lean_dec_ref_known(v_ks_1387_, 2);
v___x_1392_ = l_Lake_Toml_RBDict_alter___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert_spec__4(v_kRef_1385_, v_head_1390_, v_tail_1391_, v_newV_1388_, v_k_1386_, v_t_1384_);
return v___x_1392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1___boxed(lean_object* v_sz_1393_, lean_object* v_i_1394_, lean_object* v_bs_1395_){
_start:
{
size_t v_sz_boxed_1396_; size_t v_i_boxed_1397_; lean_object* v_res_1398_; 
v_sz_boxed_1396_ = lean_unbox_usize(v_sz_1393_);
lean_dec(v_sz_1393_);
v_i_boxed_1397_ = lean_unbox_usize(v_i_1394_);
lean_dec(v_i_1394_);
v_res_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__1(v_sz_boxed_1396_, v_i_boxed_1397_, v_bs_1395_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0___boxed(lean_object* v_ref_1399_, lean_object* v_as_1400_, lean_object* v_i_1401_, lean_object* v_stop_1402_, lean_object* v_b_1403_){
_start:
{
size_t v_i_boxed_1404_; size_t v_stop_boxed_1405_; lean_object* v_res_1406_; 
v_i_boxed_1404_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_stop_boxed_1405_ = lean_unbox_usize(v_stop_1402_);
lean_dec(v_stop_1402_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_simpVal_spec__0(v_ref_1399_, v_as_1400_, v_i_boxed_1404_, v_stop_boxed_1405_, v_b_1403_);
lean_dec_ref(v_as_1400_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(lean_object* v_as_1407_, size_t v_i_1408_, size_t v_stop_1409_, lean_object* v_b_1410_){
_start:
{
lean_object* v___y_1412_; uint8_t v___x_1416_; 
v___x_1416_ = lean_usize_dec_eq(v_i_1408_, v_stop_1409_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v_ref_1418_; lean_object* v_key_1419_; lean_object* v_val_1420_; lean_object* v___x_1421_; 
v___x_1417_ = lean_array_uget_borrowed(v_as_1407_, v_i_1408_);
v_ref_1418_ = lean_ctor_get(v___x_1417_, 0);
v_key_1419_ = lean_ctor_get(v___x_1417_, 1);
v_val_1420_ = lean_ctor_get(v___x_1417_, 2);
lean_inc(v_key_1419_);
v___x_1421_ = l_Lean_Name_components(v_key_1419_);
if (lean_obj_tag(v___x_1421_) == 0)
{
v___y_1412_ = v_b_1410_;
goto v___jp_1411_;
}
else
{
lean_object* v_head_1422_; lean_object* v_tail_1423_; lean_object* v___x_1424_; 
v_head_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_head_1422_);
v_tail_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_tail_1423_);
lean_dec_ref_known(v___x_1421_, 2);
lean_inc_ref(v_val_1420_);
lean_inc(v_ref_1418_);
v___x_1424_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_insert(v_b_1410_, v_ref_1418_, v_head_1422_, v_tail_1423_, v_val_1420_);
v___y_1412_ = v___x_1424_;
goto v___jp_1411_;
}
}
else
{
return v_b_1410_;
}
v___jp_1411_:
{
size_t v___x_1413_; size_t v___x_1414_; 
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1408_, v___x_1413_);
v_i_1408_ = v___x_1414_;
v_b_1410_ = v___y_1412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0___boxed(lean_object* v_as_1425_, lean_object* v_i_1426_, lean_object* v_stop_1427_, lean_object* v_b_1428_){
_start:
{
size_t v_i_boxed_1429_; size_t v_stop_boxed_1430_; lean_object* v_res_1431_; 
v_i_boxed_1429_ = lean_unbox_usize(v_i_1426_);
lean_dec(v_i_1426_);
v_stop_boxed_1430_ = lean_unbox_usize(v_stop_1427_);
lean_dec(v_stop_1427_);
v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_as_1425_, v_i_boxed_1429_, v_stop_boxed_1430_, v_b_1428_);
lean_dec_ref(v_as_1425_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(lean_object* v_items_1432_){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1433_ = lean_obj_once(&l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0, &l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0_once, _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__0);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_array_get_size(v_items_1432_);
v___x_1436_ = lean_nat_dec_lt(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
return v___x_1433_;
}
else
{
size_t v___x_1437_; size_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = lean_usize_of_nat(v___x_1435_);
v___x_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable_spec__0(v_items_1432_, v___x_1437_, v___x_1438_, v___x_1433_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable___boxed(lean_object* v_items_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1440_);
lean_dec_ref(v_items_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(lean_object* v_x_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
lean_inc(v_a_1444_);
lean_inc_ref(v_a_1443_);
v___x_1447_ = lean_apply_4(v_x_1442_, v___x_1446_, v_a_1443_, v_a_1444_, lean_box(0));
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v_snd_1452_; lean_object* v_items_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v_snd_1452_ = lean_ctor_get(v_a_1448_, 1);
lean_inc(v_snd_1452_);
lean_dec(v_a_1448_);
v_items_1453_ = lean_ctor_get(v_snd_1452_, 5);
lean_inc_ref(v_items_1453_);
lean_dec(v_snd_1452_);
v___x_1454_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1453_);
lean_dec_ref(v_items_1453_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1454_);
v___x_1456_ = v___x_1450_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1447_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1447_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run___boxed(lean_object* v_x_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_TomlElabM_run(v_x_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1481_) == 1)
{
lean_object* v_pre_1482_; 
v_pre_1482_ = lean_ctor_get(v_x_1481_, 0);
switch(lean_obj_tag(v_pre_1482_))
{
case 1:
{
lean_object* v_pre_1483_; 
v_pre_1483_ = lean_ctor_get(v_pre_1482_, 0);
switch(lean_obj_tag(v_pre_1483_))
{
case 0:
{
lean_object* v_str_1484_; lean_object* v_str_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v_str_1484_ = lean_ctor_get(v_x_1481_, 1);
v_str_1485_ = lean_ctor_get(v_pre_1482_, 1);
v___x_1486_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__0));
v___x_1487_ = lean_string_dec_eq(v_str_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__1));
v___x_1489_ = lean_string_dec_eq(v_str_1485_, v___x_1488_);
if (v___x_1489_ == 0)
{
return v___x_1489_;
}
else
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__2));
v___x_1491_ = lean_string_dec_eq(v_str_1484_, v___x_1490_);
if (v___x_1491_ == 0)
{
return v___x_1491_;
}
else
{
return v_suppressElabErrors_1480_;
}
}
}
else
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__3));
v___x_1493_ = lean_string_dec_eq(v_str_1484_, v___x_1492_);
if (v___x_1493_ == 0)
{
return v___x_1493_;
}
else
{
return v_suppressElabErrors_1480_;
}
}
}
case 1:
{
lean_object* v_pre_1494_; 
v_pre_1494_ = lean_ctor_get(v_pre_1483_, 0);
if (lean_obj_tag(v_pre_1494_) == 0)
{
lean_object* v_str_1495_; lean_object* v_str_1496_; lean_object* v_str_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_str_1495_ = lean_ctor_get(v_x_1481_, 1);
v_str_1496_ = lean_ctor_get(v_pre_1482_, 1);
v_str_1497_ = lean_ctor_get(v_pre_1483_, 1);
v___x_1498_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__4));
v___x_1499_ = lean_string_dec_eq(v_str_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
return v___x_1499_;
}
else
{
lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__5));
v___x_1501_ = lean_string_dec_eq(v_str_1496_, v___x_1500_);
if (v___x_1501_ == 0)
{
return v___x_1501_;
}
else
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__6));
v___x_1503_ = lean_string_dec_eq(v_str_1495_, v___x_1502_);
if (v___x_1503_ == 0)
{
return v___x_1503_;
}
else
{
return v_suppressElabErrors_1480_;
}
}
}
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
return v___x_1504_;
}
}
default: 
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
case 0:
{
lean_object* v_str_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v_str_1506_ = lean_ctor_get(v_x_1481_, 1);
v___x_1507_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___closed__7));
v___x_1508_ = lean_string_dec_eq(v_str_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
return v___x_1508_;
}
else
{
return v_suppressElabErrors_1480_;
}
}
default: 
{
uint8_t v___x_1509_; 
v___x_1509_ = 0;
return v___x_1509_;
}
}
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = 0;
return v___x_1510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_1511_, lean_object* v_x_1512_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1513_; uint8_t v_res_1514_; lean_object* v_r_1515_; 
v_suppressElabErrors_boxed_1513_ = lean_unbox(v_suppressElabErrors_1511_);
v_res_1514_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_1513_, v_x_1512_);
lean_dec(v_x_1512_);
v_r_1515_ = lean_box(v_res_1514_);
return v_r_1515_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(lean_object* v_opts_1516_, lean_object* v_opt_1517_){
_start:
{
lean_object* v_name_1518_; lean_object* v_defValue_1519_; lean_object* v_map_1520_; lean_object* v___x_1521_; 
v_name_1518_ = lean_ctor_get(v_opt_1517_, 0);
v_defValue_1519_ = lean_ctor_get(v_opt_1517_, 1);
v_map_1520_ = lean_ctor_get(v_opts_1516_, 0);
v___x_1521_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1520_, v_name_1518_);
if (lean_obj_tag(v___x_1521_) == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = lean_unbox(v_defValue_1519_);
return v___x_1522_;
}
else
{
lean_object* v_val_1523_; 
v_val_1523_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1523_);
lean_dec_ref_known(v___x_1521_, 1);
if (lean_obj_tag(v_val_1523_) == 1)
{
uint8_t v_v_1524_; 
v_v_1524_ = lean_ctor_get_uint8(v_val_1523_, 0);
lean_dec_ref_known(v_val_1523_, 0);
return v_v_1524_;
}
else
{
uint8_t v___x_1525_; 
lean_dec(v_val_1523_);
v___x_1525_ = lean_unbox(v_defValue_1519_);
return v___x_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3___boxed(lean_object* v_opts_1526_, lean_object* v_opt_1527_){
_start:
{
uint8_t v_res_1528_; lean_object* v_r_1529_; 
v_res_1528_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v_opts_1526_, v_opt_1527_);
lean_dec_ref(v_opt_1527_);
lean_dec_ref(v_opts_1526_);
v_r_1529_ = lean_box(v_res_1528_);
return v_r_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(lean_object* v_ref_1531_, lean_object* v_msgData_1532_, uint8_t v_severity_1533_, uint8_t v_isSilent_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
lean_object* v_a_1540_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; uint8_t v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v_toCold_1551_; lean_object* v___y_1552_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; uint8_t v___y_1584_; uint8_t v___y_1585_; uint8_t v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1609_; uint8_t v___y_1610_; uint8_t v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1616_; uint8_t v___y_1617_; uint8_t v___x_1627_; uint8_t v___y_1629_; uint8_t v___x_1635_; 
v___x_1627_ = 2;
v___x_1635_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1533_, v___x_1627_);
if (v___x_1635_ == 0)
{
v___y_1629_ = v___x_1635_;
goto v___jp_1628_;
}
else
{
uint8_t v___x_1636_; 
lean_inc_ref(v_msgData_1532_);
v___x_1636_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1532_);
if (v___x_1636_ == 0)
{
v___y_1629_ = v___x_1636_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
lean_dec_ref(v_msgData_1532_);
v___x_1637_ = lean_box(0);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___y_1535_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
v___jp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1540_);
lean_ctor_set(v___x_1541_, 1, v___y_1535_);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
v___jp_1543_:
{
lean_object* v_currNamespace_1553_; lean_object* v_openDecls_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_env_1559_; lean_object* v_nextMacroScope_1560_; lean_object* v_ngen_1561_; lean_object* v_auxDeclNGen_1562_; lean_object* v_traceState_1563_; lean_object* v_cache_1564_; lean_object* v_recordedDeps_1565_; lean_object* v_messages_1566_; lean_object* v_infoState_1567_; lean_object* v_snapshotTasks_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1578_; 
v_currNamespace_1553_ = lean_ctor_get(v_toCold_1551_, 4);
v_openDecls_1554_ = lean_ctor_get(v_toCold_1551_, 5);
lean_inc(v_openDecls_1554_);
lean_inc(v_currNamespace_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_currNamespace_1553_);
lean_ctor_set(v___x_1555_, 1, v_openDecls_1554_);
v___x_1556_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___y_1545_);
lean_inc_ref(v___y_1550_);
lean_inc_ref(v___y_1546_);
v___x_1557_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1557_, 0, v___y_1546_);
lean_ctor_set(v___x_1557_, 1, v___y_1549_);
lean_ctor_set(v___x_1557_, 2, v___y_1544_);
lean_ctor_set(v___x_1557_, 3, v___y_1550_);
lean_ctor_set(v___x_1557_, 4, v___x_1556_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*5, v___y_1547_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*5 + 1, v___y_1548_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*5 + 2, v_isSilent_1534_);
v___x_1558_ = lean_st_ref_take(v___y_1552_);
v_env_1559_ = lean_ctor_get(v___x_1558_, 0);
v_nextMacroScope_1560_ = lean_ctor_get(v___x_1558_, 1);
v_ngen_1561_ = lean_ctor_get(v___x_1558_, 2);
v_auxDeclNGen_1562_ = lean_ctor_get(v___x_1558_, 3);
v_traceState_1563_ = lean_ctor_get(v___x_1558_, 4);
v_cache_1564_ = lean_ctor_get(v___x_1558_, 5);
v_recordedDeps_1565_ = lean_ctor_get(v___x_1558_, 6);
v_messages_1566_ = lean_ctor_get(v___x_1558_, 7);
v_infoState_1567_ = lean_ctor_get(v___x_1558_, 8);
v_snapshotTasks_1568_ = lean_ctor_get(v___x_1558_, 9);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1570_ = v___x_1558_;
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_snapshotTasks_1568_);
lean_inc(v_infoState_1567_);
lean_inc(v_messages_1566_);
lean_inc(v_recordedDeps_1565_);
lean_inc(v_cache_1564_);
lean_inc(v_traceState_1563_);
lean_inc(v_auxDeclNGen_1562_);
lean_inc(v_ngen_1561_);
lean_inc(v_nextMacroScope_1560_);
lean_inc(v_env_1559_);
lean_dec(v___x_1558_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1578_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1572_ = lean_box(0);
v___x_1573_ = l_Lean_MessageLog_add(v___x_1557_, v_messages_1566_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 7, v___x_1573_);
v___x_1575_ = v___x_1570_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_env_1559_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_nextMacroScope_1560_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_ngen_1561_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_auxDeclNGen_1562_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_traceState_1563_);
lean_ctor_set(v_reuseFailAlloc_1577_, 5, v_cache_1564_);
lean_ctor_set(v_reuseFailAlloc_1577_, 6, v_recordedDeps_1565_);
lean_ctor_set(v_reuseFailAlloc_1577_, 7, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1577_, 8, v_infoState_1567_);
lean_ctor_set(v_reuseFailAlloc_1577_, 9, v_snapshotTasks_1568_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_st_ref_put(v___y_1552_, v___x_1575_);
v_a_1540_ = v___x_1572_;
goto v___jp_1539_;
}
}
}
v___jp_1579_:
{
lean_object* v_fileName_1588_; lean_object* v_fileMap_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1604_; 
v_fileName_1588_ = lean_ctor_get(v___y_1582_, 0);
v_fileMap_1589_ = lean_ctor_get(v___y_1582_, 1);
v___x_1590_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1532_);
v___x_1591_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v___x_1590_, v___y_1536_, v___y_1537_);
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1604_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
lean_inc_ref_n(v_fileMap_1589_, 2);
v___x_1596_ = l_Lean_FileMap_toPosition(v_fileMap_1589_, v___y_1583_);
lean_dec(v___y_1583_);
v___x_1597_ = l_Lean_FileMap_toPosition(v_fileMap_1589_, v___y_1587_);
lean_dec(v___y_1587_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 1);
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
v___x_1600_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___closed__0));
if (v___y_1585_ == 0)
{
lean_dec_ref(v___y_1580_);
v___y_1544_ = v___x_1599_;
v___y_1545_ = v_a_1592_;
v___y_1546_ = v_fileName_1588_;
v___y_1547_ = v___y_1584_;
v___y_1548_ = v___y_1586_;
v___y_1549_ = v___x_1596_;
v___y_1550_ = v___x_1600_;
v_toCold_1551_ = v___y_1581_;
v___y_1552_ = v___y_1537_;
goto v___jp_1543_;
}
else
{
uint8_t v___x_1601_; 
lean_inc(v_a_1592_);
v___x_1601_ = l_Lean_MessageData_hasTag(v___y_1580_, v_a_1592_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_dec_ref(v___x_1599_);
lean_dec_ref(v___x_1596_);
lean_dec(v_a_1592_);
v___x_1602_ = lean_box(0);
v_a_1540_ = v___x_1602_;
goto v___jp_1539_;
}
else
{
v___y_1544_ = v___x_1599_;
v___y_1545_ = v_a_1592_;
v___y_1546_ = v_fileName_1588_;
v___y_1547_ = v___y_1584_;
v___y_1548_ = v___y_1586_;
v___y_1549_ = v___x_1596_;
v___y_1550_ = v___x_1600_;
v_toCold_1551_ = v___y_1581_;
v___y_1552_ = v___y_1537_;
goto v___jp_1543_;
}
}
}
}
}
v___jp_1605_:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Syntax_getTailPos_x3f(v___y_1609_, v___y_1610_);
lean_dec(v___y_1609_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_inc(v___y_1612_);
v___y_1580_ = v___y_1606_;
v___y_1581_ = v___y_1607_;
v___y_1582_ = v___y_1607_;
v___y_1583_ = v___y_1612_;
v___y_1584_ = v___y_1610_;
v___y_1585_ = v___y_1608_;
v___y_1586_ = v___y_1611_;
v___y_1587_ = v___y_1612_;
goto v___jp_1579_;
}
else
{
lean_object* v_val_1614_; 
v_val_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v___y_1580_ = v___y_1606_;
v___y_1581_ = v___y_1607_;
v___y_1582_ = v___y_1607_;
v___y_1583_ = v___y_1612_;
v___y_1584_ = v___y_1610_;
v___y_1585_ = v___y_1608_;
v___y_1586_ = v___y_1611_;
v___y_1587_ = v_val_1614_;
goto v___jp_1579_;
}
}
v___jp_1615_:
{
lean_object* v_toCold_1618_; lean_object* v_ref_1619_; uint8_t v_suppressElabErrors_1620_; lean_object* v___x_1621_; lean_object* v___f_1622_; lean_object* v_ref_1623_; lean_object* v___x_1624_; 
v_toCold_1618_ = lean_ctor_get(v___y_1536_, 0);
v_ref_1619_ = lean_ctor_get(v___y_1536_, 2);
v_suppressElabErrors_1620_ = lean_ctor_get_uint8(v___y_1536_, sizeof(void*)*3 + 2);
v___x_1621_ = lean_box(v_suppressElabErrors_1620_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1622_, 0, v___x_1621_);
v_ref_1623_ = l_Lean_replaceRef(v_ref_1531_, v_ref_1619_);
v___x_1624_ = l_Lean_Syntax_getPos_x3f(v_ref_1623_, v___y_1616_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_unsigned_to_nat(0u);
v___y_1606_ = v___f_1622_;
v___y_1607_ = v_toCold_1618_;
v___y_1608_ = v_suppressElabErrors_1620_;
v___y_1609_ = v_ref_1623_;
v___y_1610_ = v___y_1616_;
v___y_1611_ = v___y_1617_;
v___y_1612_ = v___x_1625_;
goto v___jp_1605_;
}
else
{
lean_object* v_val_1626_; 
v_val_1626_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v___x_1624_, 1);
v___y_1606_ = v___f_1622_;
v___y_1607_ = v_toCold_1618_;
v___y_1608_ = v_suppressElabErrors_1620_;
v___y_1609_ = v_ref_1623_;
v___y_1610_ = v___y_1616_;
v___y_1611_ = v___y_1617_;
v___y_1612_ = v_val_1626_;
goto v___jp_1605_;
}
}
v___jp_1628_:
{
uint8_t v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = 1;
v___x_1631_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1533_, v___x_1630_);
if (v___x_1631_ == 0)
{
v___y_1616_ = v___y_1629_;
v___y_1617_ = v_severity_1533_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1632_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1536_);
v___x_1633_ = l_Lean_warningAsError;
v___x_1634_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2_spec__3(v___x_1632_, v___x_1633_);
lean_dec_ref(v___x_1632_);
if (v___x_1634_ == 0)
{
v___y_1616_ = v___y_1629_;
v___y_1617_ = v_severity_1533_;
goto v___jp_1615_;
}
else
{
v___y_1616_ = v___y_1629_;
v___y_1617_ = v___x_1627_;
goto v___jp_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2___boxed(lean_object* v_ref_1640_, lean_object* v_msgData_1641_, lean_object* v_severity_1642_, lean_object* v_isSilent_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v_severity_boxed_1648_; uint8_t v_isSilent_boxed_1649_; lean_object* v_res_1650_; 
v_severity_boxed_1648_ = lean_unbox(v_severity_1642_);
v_isSilent_boxed_1649_ = lean_unbox(v_isSilent_1643_);
v_res_1650_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1640_, v_msgData_1641_, v_severity_boxed_1648_, v_isSilent_boxed_1649_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v_ref_1640_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(lean_object* v_ref_1651_, lean_object* v_msgData_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
uint8_t v___x_1657_; uint8_t v___x_1658_; lean_object* v___x_1659_; 
v___x_1657_ = 2;
v___x_1658_ = 0;
v___x_1659_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1_spec__2(v_ref_1651_, v_msgData_1652_, v___x_1657_, v___x_1658_, v___y_1653_, v___y_1654_, v___y_1655_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1___boxed(lean_object* v_ref_1660_, lean_object* v_msgData_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_ref_1660_, v_msgData_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v_ref_1660_);
return v_res_1666_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__0));
v___x_1670_ = l_Lean_MessageData_ofFormat(v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(uint8_t v_recovering_1671_, lean_object* v_as_1672_, size_t v_sz_1673_, size_t v_i_1674_, uint8_t v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_snd_1681_; lean_object* v_snd_1682_; lean_object* v_a_1688_; uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_box(v_b_1675_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v___y_1676_);
v___x_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
return v___x_1710_;
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1712_; uint8_t v_recovering_1713_; 
v_a_1711_ = lean_array_uget_borrowed(v_as_1672_, v_i_1674_);
v___x_1712_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval___closed__1));
lean_inc(v_a_1711_);
v_recovering_1713_ = l_Lean_Syntax_isOfKind(v_a_1711_, v___x_1712_);
if (v_recovering_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable___closed__2));
lean_inc(v_a_1711_);
v___x_1715_ = l_Lean_Syntax_isOfKind(v_a_1711_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; uint8_t v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable___closed__1));
lean_inc(v_a_1711_);
v___x_1717_ = l_Lean_Syntax_isOfKind(v_a_1711_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___closed__1);
lean_inc_ref(v___y_1676_);
v___x_1719_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v_a_1711_, v___x_1718_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v_snd_1721_; lean_object* v___x_1722_; 
lean_dec_ref(v___y_1676_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v_snd_1721_ = lean_ctor_get(v_a_1720_, 1);
lean_inc(v_snd_1721_);
lean_dec(v_a_1720_);
v___x_1722_ = lean_box(v_b_1675_);
v_snd_1681_ = v___x_1722_;
v_snd_1682_ = v_snd_1721_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1723_; 
v_a_1723_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1719_, 1);
v_a_1688_ = v_a_1723_;
goto v___jp_1687_;
}
}
else
{
lean_object* v___x_1724_; 
lean_inc_ref(v___y_1676_);
lean_inc(v_a_1711_);
v___x_1724_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabArrayTable(v_a_1711_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v_snd_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___y_1676_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v_snd_1726_ = lean_ctor_get(v_a_1725_, 1);
lean_inc(v_snd_1726_);
lean_dec(v_a_1725_);
v___x_1727_ = lean_box(v_recovering_1713_);
v_snd_1681_ = v___x_1727_;
v_snd_1682_ = v_snd_1726_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1728_; 
v_a_1728_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1724_, 1);
v_a_1688_ = v_a_1728_;
goto v___jp_1687_;
}
}
}
else
{
lean_object* v___x_1729_; 
lean_inc_ref(v___y_1676_);
lean_inc(v_a_1711_);
v___x_1729_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabStdTable(v_a_1711_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v_snd_1731_; lean_object* v___x_1732_; 
lean_dec_ref(v___y_1676_);
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v_snd_1731_ = lean_ctor_get(v_a_1730_, 1);
lean_inc(v_snd_1731_);
lean_dec(v_a_1730_);
v___x_1732_ = lean_box(v_recovering_1713_);
v_snd_1681_ = v___x_1732_;
v_snd_1682_ = v_snd_1731_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1729_, 1);
v_a_1688_ = v_a_1733_;
goto v___jp_1687_;
}
}
}
else
{
if (v_b_1675_ == 0)
{
lean_object* v___x_1734_; 
lean_inc_ref(v___y_1676_);
lean_inc(v_a_1711_);
v___x_1734_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabKeyval(v_a_1711_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v_snd_1736_; lean_object* v___x_1737_; 
lean_dec_ref(v___y_1676_);
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v_snd_1736_ = lean_ctor_get(v_a_1735_, 1);
lean_inc(v_snd_1736_);
lean_dec(v_a_1735_);
v___x_1737_ = lean_box(v_b_1675_);
v_snd_1681_ = v___x_1737_;
v_snd_1682_ = v_snd_1736_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1734_, 1);
v_a_1688_ = v_a_1738_;
goto v___jp_1687_;
}
}
else
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_box(v_b_1675_);
v_snd_1681_ = v___x_1739_;
v_snd_1682_ = v___y_1676_;
goto v___jp_1680_;
}
}
}
v___jp_1680_:
{
size_t v___x_1683_; size_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1674_, v___x_1683_);
v___x_1685_ = lean_unbox(v_snd_1681_);
lean_dec(v_snd_1681_);
v_i_1674_ = v___x_1684_;
v_b_1675_ = v___x_1685_;
v___y_1676_ = v_snd_1682_;
goto _start;
}
v___jp_1687_:
{
uint8_t v___x_1689_; 
v___x_1689_ = l_Lean_Exception_isInterrupt(v_a_1688_);
if (v___x_1689_ == 0)
{
uint8_t v___x_1690_; 
lean_inc_ref(v_a_1688_);
v___x_1690_ = l_Lean_Exception_isRuntime(v_a_1688_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = l_Lean_Exception_getRef(v_a_1688_);
v___x_1692_ = l_Lean_Exception_toMessageData(v_a_1688_);
v___x_1693_ = l_Lean_logErrorAt___at___00Lake_Toml_elabToml_spec__1(v___x_1691_, v___x_1692_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___x_1691_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v_snd_1695_; lean_object* v___x_1696_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v_snd_1695_ = lean_ctor_get(v_a_1694_, 1);
lean_inc(v_snd_1695_);
lean_dec(v_a_1694_);
v___x_1696_ = lean_box(v_recovering_1671_);
v_snd_1681_ = v___x_1696_;
v_snd_1682_ = v_snd_1695_;
goto v___jp_1680_;
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
v_a_1697_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1693_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1693_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v___x_1705_; 
lean_dec_ref(v___y_1676_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1688_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1706_; 
lean_dec_ref(v___y_1676_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_a_1688_);
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2___boxed(lean_object* v_recovering_1740_, lean_object* v_as_1741_, lean_object* v_sz_1742_, lean_object* v_i_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
uint8_t v_recovering_boxed_1749_; size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; uint8_t v_b_boxed_1752_; lean_object* v_res_1753_; 
v_recovering_boxed_1749_ = lean_unbox(v_recovering_1740_);
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1742_);
lean_dec(v_sz_1742_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1743_);
lean_dec(v_i_1743_);
v_b_boxed_1752_ = lean_unbox(v_b_1744_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_boxed_1749_, v_as_1741_, v_sz_boxed_1750_, v_i_boxed_1751_, v_b_boxed_1752_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_as_1741_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_ref_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v_ref_1758_ = lean_ctor_get(v___y_1755_, 2);
v___x_1759_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Expression_0__Lake_Toml_elabSubKeys_spec__0_spec__0_spec__1(v_msg_1754_, v___y_1755_, v___y_1756_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc(v_ref_1758_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v_ref_1758_);
lean_ctor_set(v___x_1764_, 1, v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(lean_object* v_ref_1774_, lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_toCold_1779_; lean_object* v_currRecDepth_1780_; lean_object* v_ref_1781_; uint16_t v_optionFlags_1782_; uint8_t v_suppressElabErrors_1783_; uint8_t v_checkDeprecated_1784_; uint8_t v_isRecordingDeps_1785_; lean_object* v_ref_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_toCold_1779_ = lean_ctor_get(v___y_1776_, 0);
v_currRecDepth_1780_ = lean_ctor_get(v___y_1776_, 1);
v_ref_1781_ = lean_ctor_get(v___y_1776_, 2);
v_optionFlags_1782_ = lean_ctor_get_uint16(v___y_1776_, sizeof(void*)*3);
v_suppressElabErrors_1783_ = lean_ctor_get_uint8(v___y_1776_, sizeof(void*)*3 + 2);
v_checkDeprecated_1784_ = lean_ctor_get_uint8(v___y_1776_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1785_ = lean_ctor_get_uint8(v___y_1776_, sizeof(void*)*3 + 4);
v_ref_1786_ = l_Lean_replaceRef(v_ref_1774_, v_ref_1781_);
lean_inc(v_currRecDepth_1780_);
lean_inc_ref(v_toCold_1779_);
v___x_1787_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1787_, 0, v_toCold_1779_);
lean_ctor_set(v___x_1787_, 1, v_currRecDepth_1780_);
lean_ctor_set(v___x_1787_, 2, v_ref_1786_);
lean_ctor_set_uint16(v___x_1787_, sizeof(void*)*3, v_optionFlags_1782_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 2, v_suppressElabErrors_1783_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 3, v_checkDeprecated_1784_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 4, v_isRecordingDeps_1785_);
v___x_1788_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1775_, v___x_1787_, v___y_1777_);
lean_dec_ref_known(v___x_1787_, 3);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg___boxed(lean_object* v_ref_1789_, lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1789_, v_msg_1790_, v___y_1791_, v___y_1792_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v_ref_1789_);
return v_res_1794_;
}
}
static lean_object* _init_l_Lake_Toml_elabToml___closed__3(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__2));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml(lean_object* v_x_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__1));
lean_inc(v_x_1807_);
v___x_1812_ = l_Lean_Syntax_isOfKind(v_x_1807_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1814_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1807_, v___x_1813_, v_a_1808_, v_a_1809_);
lean_dec(v_x_1807_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v_recovering_1818_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = l_Lean_Syntax_getArg(v_x_1807_, v___x_1815_);
v___x_1817_ = ((lean_object*)(l_Lake_Toml_elabToml___closed__4));
v_recovering_1818_ = l_Lean_Syntax_isOfKind(v___x_1816_, v___x_1817_);
if (v_recovering_1818_ == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l_Lake_Toml_elabToml___closed__3, &l_Lake_Toml_elabToml___closed__3_once, _init_l_Lake_Toml_elabToml___closed__3);
v___x_1820_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_x_1807_, v___x_1819_, v_a_1808_, v_a_1809_);
lean_dec(v_x_1807_);
return v___x_1820_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v_xs_1823_; uint8_t v_recovering_1824_; lean_object* v___x_1825_; size_t v_sz_1826_; size_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1821_ = lean_unsigned_to_nat(1u);
v___x_1822_ = l_Lean_Syntax_getArg(v_x_1807_, v___x_1821_);
lean_dec(v_x_1807_);
v_xs_1823_ = l_Lean_Syntax_getArgs(v___x_1822_);
lean_dec(v___x_1822_);
v_recovering_1824_ = 0;
v___x_1825_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1823_);
lean_dec_ref(v_xs_1823_);
v_sz_1826_ = lean_array_size(v___x_1825_);
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = ((lean_object*)(l_Lake_Toml_instInhabitedElabState_default___closed__1));
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_Toml_elabToml_spec__2(v_recovering_1818_, v___x_1825_, v_sz_1826_, v___x_1827_, v_recovering_1824_, v___x_1828_, v_a_1808_, v_a_1809_);
lean_dec_ref(v___x_1825_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1840_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_snd_1834_; lean_object* v_items_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v_snd_1834_ = lean_ctor_get(v_a_1830_, 1);
lean_inc(v_snd_1834_);
lean_dec(v_a_1830_);
v_items_1835_ = lean_ctor_get(v_snd_1834_, 5);
lean_inc_ref(v_items_1835_);
lean_dec(v_snd_1834_);
v___x_1836_ = l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_mkSimpleTable(v_items_1835_);
lean_dec_ref(v_items_1835_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1836_);
v___x_1838_ = v___x_1832_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1829_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1829_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabToml___boxed(lean_object* v_x_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lake_Toml_elabToml(v_x_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(lean_object* v_00_u03b1_1854_, lean_object* v_ref_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___redArg(v_ref_1855_, v_msg_1856_, v___y_1857_, v___y_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_ref_1862_, lean_object* v_msg_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0(v_00_u03b1_1861_, v_ref_1862_, v_msg_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v_ref_1862_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(lean_object* v_00_u03b1_1868_, lean_object* v_msg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___redArg(v_msg_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lake_Toml_elabToml_spec__0_spec__0(v_00_u03b1_1874_, v_msg_1875_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1879_;
}
}
lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_instInhabitedKeyTy_default = _init_l_Lake_Toml_instInhabitedKeyTy_default();
l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy = _init_l___private_Lake_Toml_Elab_Expression_0__Lake_Toml_instInhabitedKeyTy();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_Elab_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Elab_Expression(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Elab_Expression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Elab_Expression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Elab_Expression(builtin);
}
#ifdef __cplusplus
}
#endif
